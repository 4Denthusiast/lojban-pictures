module VectorToPixel

import Picture

import Control.Algebra
import Data.List
import Data.Vect
import Graphics.SDL2.SDLTTF

%include C "timer.h"
%link C "timer.o"
%include C "graphics.h"
%link C "graphics.o"

lineWeight : Double
lineWeight = 0.1

getTime : IO Double
getTime = foreign FFI_C "doubleTime" (IO Double)

printTime : String -> IO a -> IO a
printTime s mx = do
    start <- getTime
    x <- mx
    end <- getTime
    putStrLn ("Time for " ++ s ++ ": " ++ show (end - start))
    pure x

-- TODO: optimise for the particular use case, with long forward and backward runs.
sortOn : (Ord b) => (a -> b) -> List a -> List a
sortOn f = map snd . sortBy (\(x,_), (y,_) => compare x y) . map (\x => (f x, x))

mapPreservesNonempty : {l : List a} -> {f : a -> b} -> NonEmpty l -> NonEmpty (map f l)
mapPreservesNonempty {l=(x::xs)} {f} IsNonEmpty = IsNonEmpty

drawDot : Double -> Int -> Int -> Ptr -> Point -> IO ()
drawDot s w h tex [cx,cy] = foreign FFI_C "drawCircle" (Ptr -> Int -> Int -> Double -> Double -> Double -> Double -> IO ()) tex w h cx cy 0 (lineWeight * s)

segmentBeziers : List (BezierPointType, Point) -> (Bool, List (Bool, List Point))
segmentBeziers [] = (False, [])
segmentBeziers ((t0,p0)::ps0) = if t0 == Control
        then (False, segment' ((t0,p0)::ps0))
        else (True, segment' ((t0,p0)::ps0++[(Control,p0)]))
    where segment' : List (BezierPointType, Point) -> List (Bool, List Point)
          segment' [] = []
          segment' ((t1,p)::ps) = let (psl,psr) = span ((==Control).fst) ps in (t1==Corner,p::map snd (psl ++ take 1 psr))::segment' psr

bezierToLines : Double -> Int -> Int -> List Point -> List Point
bezierToLines s w h [] = []
bezierToLines s w h (p::ps0) = p :: splitUntil 10 (p::fromList ps0)
    where tolerance : Double
          tolerance = 0.2 --How far the lines may deviate from the curve, in pixels. This should be less than 1 to get good antialiasing.
          straightEnough : Vect (S len) Point -> Bool
          straightEnough c = let
                  a = head c
                  b = last c
                  ab2 = dot (a <-> b) (a <-> b)
                  ax = head a
                  ay = head (tail a)
                  bx = head b
                  by = head (tail b)
                  tolerance = max 0.2 $ (\d => (d-s*lineWeight/2)/2) $ foldl1 max $ the (List Double) [min (-ax) (-bx), min (-ay) (-by), (min ax bx-cast w), (min ay by-cast h)] -- The tolerance for things on-screen is less than 1px to allow for smooth antialiasing.
              in all (\p => dot (p <-> a) (p <-> a) <= ab2 && dot (p <-> a) (b <-> a) >= 0 && dot (p <-> b) (a <-> b) >= 0 && tolerance >= abs (cross (p <-> a) (b <-> a)/sqrt ab2)) c
          firstHalf : Vect n Point -> Vect n Point
          firstHalf [] = []
          firstHalf (p0::ps) = p0 :: firstHalf (zipWith (\p, p' => map (/2) $ p <+> p') (init (p0::ps)) ps)
          secondHalf : Vect n Point -> Vect n Point
          secondHalf ps = reverse $ firstHalf $ reverse ps
          splitUntil : Nat -> Vect (S n) Point -> List Point
          splitUntil Z ps = [last ps]
          splitUntil (S t) ps = if straightEnough ps then splitUntil 0 ps else splitUntil t (firstHalf ps) ++ splitUntil t (secondHalf ps)

mergeCurves : List (Bool, List Point) -> List (Bool, Point)
mergeCurves [] = []
mergeCurves ((_,[])::cs) = mergeCurves cs --I don't think this case is possible, but it's awkward to prove that so I'm just leaving it in.
mergeCurves ((b,p::ps)::cs) = mergeCurves' b p ps cs
    where mergeCurves' : Bool -> Point -> List Point -> List (Bool, List Point) -> List (Bool, Point)
          mergeCurves' b p [] [] = [(b,p)]
          mergeCurves' b p [] ((b',ps)::cs) = mergeCurves' (b || b') p ps cs
          mergeCurves' b p (p'::ps) cs = if p == p'
              then mergeCurves' b p ps cs
              else (b,p)::mergeCurves' False p' ps cs

-- MkLine a b c represents the locus of points such that ax+by=c.
data Line = MkLine Double Double Double

Segment : Type
Segment = (Point,Line,Point)

makeLine : Double -> Double -> Double -> Line
makeLine a b c = MkLine (a/l) (b/l) (c/l)
    where l = sqrt (a*a + b*b)

lineThrough : Point -> Point -> Line
lineThrough [x,y] [x',y'] = makeLine (y-y') (x'-x) (-x*y'+y*x')

offsetLine : Double -> Line -> Line
offsetLine o (MkLine a b c) = MkLine a b (c+o)

flipLine : Line -> Line
flipLine (MkLine a b c) = MkLine (-a) (-b) (-c)

{-
ax+by=c
Ax+By=C

Bay-bAy=Ca-cA
-}
intersection : Line -> Line -> Point
intersection (MkLine a b c) (MkLine a' b' c') = [(c*b'-c'*b)/det,(c'*a-c*a')/det]
    where det = a*b'-b*a'

rotate : {a:Type} -> {n:Nat} -> Vect (S n) a -> Vect (S n) a
rotate {a} {n} (x::xs) = replace {P=(\n' => Vect n' a)} (trans (plusCommutative n 1) (plusOneSucc n)) $ xs ++ [x]

intersections : Vect (S n) Line -> Vect (S n) Segment
intersections ls = zip3 ps (rotate ls) (rotate ps)
    where ps = zipWith intersection ls (rotate ls)

thickenCurve : {n:Nat} -> Double -> (Bool, Vect n (Bool, Point)) -> List Segment
thickenCurve s (_, []) = []
thickenCurve s (_, [(b0,p0)]) = [] --TODO: I guess substitute in point rendering somehow?
thickenCurve s (True, [p0,p1]) = thickenCurve s (False, [p0,p1])
-- TODO: I can probably unify these latter two cases again.
thickenCurve {n=S (S n')} s (True, ps) = toList $ intersections $ flipLine closeLine :: (lines ++ (closeLine :: otherLines))
    where n : Nat
          n = S n'
          ps' : Vect (S (S n')) Point
          ps' = map snd ps
          lines : Vect n Line
          lines = map (offsetLine (lineWeight*s/2)) $ zipWith lineThrough (init ps') (tail ps')
          otherLines : Vect n Line
          otherLines = map (offsetLine (lineWeight*s) . flipLine) (reverse lines)
          closePoint : Vect n Line -> Point
          closePoint ls = intersection (head ls) (last ls)
          closeLine = lineThrough (closePoint lines) (closePoint otherLines)
thickenCurve {n=S (S n')} s (False, ps) = toList $ intersections $ map (offsetLine (lineWeight*s/2)) $ endCap ps' :: (lines ++ (endCap $ reverse ps') :: otherLines)
    where ps' : Vect (S (S n')) Point
          ps' = map snd ps
          lines : Vect (S n') Line
          lines = zipWith lineThrough (init ps') (tail ps')
          otherLines : Vect (S n') Line
          otherLines = map flipLine (reverse lines)
          endCap ([x,y]::[x',y']::_) = makeLine (x-x') (y-y') (x*(x-x')+y*(y-y'))

fillPolygon : Ptr -> Int -> Int -> List Segment -> IO ()
fillPolygon tex w h [] = pure ()
fillPolygon tex w h (pl::pls) = foreign FFI_C "fillPolygon" (Ptr -> Int -> Int -> Int -> Int -> Int -> Int -> Raw (List Segment) -> IO ()) tex w h (fst xRange) (snd xRange) (fst yRange) (snd yRange) $ MkRaw $ sortOn (Data.Vect.head . tail . fst) $ map orient (pl::pls)
    where ps : List Point
          ps = map fst (pl::pls)
          psne : NonEmpty ps
          psne = mapPreservesNonempty IsNonEmpty
          rangeOf : Int -> (l:List Double) -> {ok:NonEmpty l} -> (Int,Int)
          rangeOf lim xs = let
                  low = cast $ floor $ foldr1 min xs
                  high = cast $ ceiling $ foldr1 max xs
              in if low >= lim || high < -1 then (0,0) else ((max (-1) low),(min lim high))
          xRange : (Int,Int)
          xRange = rangeOf w {ok=mapPreservesNonempty psne} $ map head ps
          yRange : (Int,Int)
          yRange = rangeOf h {ok=mapPreservesNonempty psne} $ map (Data.Vect.index 1) ps
          orient : Segment -> Segment
          orient ([x0,y0],l,[x1,y1]) = if y0 <= y1 then ([x0,y0],l,[x1,y1]) else ([x1,y1],l,[x0,y0])

drawBeziers : Double -> Int -> Int -> Ptr -> List (BezierPointType, Point) -> IO ()
drawBeziers s w h tex ps = fillPolygon tex w h $ thickenCurve s (fst closeAndCurve, fromList singleCurve)
    where closeAndCurve : Pair Bool (List (Bool, Point))
          closeAndCurve = map mergeCurves $ map (map (map (bezierToLines s w h))) $ segmentBeziers ps
          singleCurve = snd closeAndCurve

drawBezier : Double -> Int -> Int -> Ptr -> Vect 4 Point -> IO ()
drawBezier s w h tex ps = drawBeziers s w h tex $ toList $ map (\p => (Control,p)) ps

drawLine : Double -> Int -> Int -> Ptr -> Point -> Point -> IO ()
drawLine s w h tex p0 p1 = drawBeziers s w h tex [(Control,p0),(Control,p1)]

drawCircle : Double -> Int -> Int -> Ptr -> Point -> Double -> IO ()
drawCircle s w h tex [cx,cy] r = foreign FFI_C "drawCircle" (Ptr -> Int -> Int -> Double -> Double -> Double -> Double -> IO ()) tex w h cx cy (r-weight) (r+weight)
    where weight : Double
          weight = lineWeight * s / 2

export
drawRaw : Double -> Transform -> Ptr -> Int -> Int -> SDLFont -> Picture -> IO ()
drawRaw s t tex w h font pic = if culled (transformHull t $ pictureHull pic) then pure () else case pic of
        Dot p => drawDot s w h tex (applyTransform t p)
        Line p p' => drawLine s w h tex (applyTransform t p) (applyTransform t p')
        Bezier ps => drawBezier s w h tex (map (applyTransform t) ps)
        Beziers ps => drawBeziers s w h tex (map (map $ applyTransform t) ps)
        Circle p r => drawCircle s w h tex (applyTransform t p) (r * scale t)
        Text text => pure ()
        Transformed t' pic' => drawRaw s (t <+> t') tex w h font pic'
        Pictures pics _ => for_ pics (drawRaw s t tex w h font)
    where weight : Double
          weight = lineWeight * s
          culled (MkHull pts) = all (\[x,_] => x < -weight) pts || all (\[_,y] => y < -weight) pts || all (\[x,_] => x > cast w + weight) pts || all (\[_,y] => y > cast h + weight) pts
