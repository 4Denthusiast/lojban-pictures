module VectorToPixel

import Picture

import Control.Algebra
import Data.List
import Data.Vect
import Graphics.SDL2.SDLTTF

lineWeight : Double
lineWeight = 0.1

public export
Colour : Type
Colour = (Bits8,Bits8,Bits8)

Reader : Type
Reader = Int -> Int -> IO Colour

Writer : Type
Writer = Int -> Int -> Colour -> IO ()

Ink : Type
Ink = Int -> Int -> Double -> IO ()

-- TODO: optimise for the particular use case, with long forward and backward runs.
sortOn : (Ord b) => (a -> b) -> List a -> List a
sortOn f = map snd . sortBy (\(x,_), (y,_) => compare x y) . map (\x => (f x, x))

mapPreservesNonempty : {l : List a} -> {f : a -> b} -> NonEmpty l -> NonEmpty (map f l)
mapPreservesNonempty {l=(x::xs)} {f} IsNonEmpty = IsNonEmpty

drawDot : Double -> Ink -> Point -> IO ()
drawDot s ink [cx,cy] = for_ [(cast $ floor $ cy - weight - 0.5)..(cast $ ceiling $ cy + weight + 0.5)] (\y =>
        for_ [(cast $ floor $ cx - weight - 0.5)..(cast $ ceiling $ cx + weight + 0.5)] (\x => renderPoint x y)
    )
    where weight : Double
          weight = lineWeight * s -- the width is twice the line weight, otherwise dots are too small.
          renderPoint : Int -> Int -> IO ()
          renderPoint x y = let
                  r = sqrt $ (cast x - cx)*(cast x - cx) + (cast y - cy)*(cast y-cy)
                  c = 1 - max 0 (r-weight+0.5)
              in if c > 0 then ink x y c else pure ()

drawPlainLine : Ink -> Point -> Point -> IO ()
drawPlainLine ink [x0,y0] [x1,y1] = if abs (x0 - x1) < abs (y0 - y1) then l' (flip ink) [y0,x0] [y1,x1] else l' ink [x0,y0] [x1,y1]
    where l'' : Ink -> Point -> Point -> IO ()
          l'' ink' [x,y] [x',y'] = for_ (the (List Int) [(cast x)..(cast x')]) (\cx => ink' cx (cast $ y + (y'-y)* (cast cx-x)/(x'-x)) 1)
          l' : Ink -> Point -> Point -> IO ()
          l' ink' [x,y] [x',y'] = if x < x' then l'' ink' [x,y] [x',y'] else l'' ink' [x',y'] [x,y]

drawHull : Ink -> ConvexHull -> IO ()
drawHull ink (MkHull []) = pure ()
drawHull ink (MkHull (p::ps)) = flip for_ (uncurry (drawPlainLine ink)) $ Prelude.List.zip (p::ps) (ps++[p])

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

horizontalIntersect : Line -> Double -> Point
horizontalIntersect (MkLine a b c) y = [(c-b*y)/a, y]

verticalIntersect : Line -> Double -> Point
verticalIntersect (MkLine a b c) x = [x, (c-a*x)/b]

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

-- Put the end that's first in the given dimension first.
orient : Fin 2 -> Segment -> Segment
orient i (p,l,p') = if index i p <= index i p' then (p,l,p') else (p',l,p)

-- This assumes the (x,y) pixel covers [x,x+1]*[y,y+1], which is inconsistent with some of the other primitives.
fillPolygon' : Ink -> List Int -> List Int -> List Segment -> List Segment -> IO ()
fillPolygon' ink xRange [] incoming segs = pure ()
fillPolygon' ink xRange (y0::yRange) incoming segs = fillLine 0 xRange [] yIntersects lines *> fillPolygon' ink xRange yRange outgoing remainingSegs
    where newSegs : List Segment
          newSegs = fst $ span (\([_,y],_) => y <= (cast y0 + 1)) segs
          remainingSegs = snd $ span (\([_,y],_) => y <= (cast y0 + 1)) segs
          trimLine : (Point, Line, Point) -> (Maybe Segment, Segment)
          trimLine (p,l,[x,y]) = if y > cast y0 + 1
              then let p' = horizontalIntersect l (cast y0 + 1) in (Just (p',l,[x,y]),(p,l,p'))
              else (Nothing, (p,l,[x,y]))
          outgoingAndLines : (List (Maybe Segment),List Segment)
          outgoingAndLines = unzip $ map trimLine (newSegs ++ incoming)
          lines = sortOn (head . fst) $ map (orient 0) $ snd outgoingAndLines
          outgoing = catMaybes $ fst outgoingAndLines
          yIntersects = sortOn fst $ map (\([xi,_],MkLine xp _ _,_) => (xi,if xp<0 then 1 else -1)) incoming
          fillLine : Int -> List Int -> List Segment -> List (Double,Int) -> List Segment -> IO ()
          fillLine covered [] incomingX is ls = pure ()
          fillLine covered (x0::xs) incomingX is ls = ink x0 y0 colour *> fillLine covered' xs outgoingX is' remainingSegsX
              where borderPoints : List (Double, Int)
                    borderPoints = fst $ span ((< cast x0 + 1).fst) is
                    covered' = (covered+) $ sum $ map snd borderPoints
                    is' = snd $ span ((< cast x0 + 1) . fst) is
                    newSegsX : List Segment
                    newSegsX = fst $ span (\([x,_],_) => x <= cast x0 + 1) ls
                    remainingSegsX : List Segment
                    remainingSegsX = snd $ span (\([x,_],_) => x <= cast x0 + 1) ls
                    trimLineX : Segment -> (Maybe Segment, Segment)
                    trimLineX (p,l,[x,y]) = if x > cast x0 + 1
                        then let p' = verticalIntersect l (cast x0 + 1) in (Just (p',l,[x,y]),(p,l,p'))
                        else (Nothing, (p,l,[x,y]))
                    outgoingAndLinesX : (List (Maybe Segment), List Segment)
                    outgoingAndLinesX = unzip $ map trimLineX $ newSegsX ++ incomingX
                    linesX : List Segment
                    linesX = snd outgoingAndLinesX
                    outgoingX : List Segment
                    outgoingX = catMaybes $ fst outgoingAndLinesX
                    borderColour : Double
                    borderColour = ((cast covered)+) $ sum $ map (\(x,s) => (cast x0+1-x)*cast s) borderPoints
                    segCovered : Segment -> Double
                    segCovered ([x,y],MkLine _ yp _,[x',y']) = (cast y0 + 1 - (y+y')/2) * (x'-x) * if yp > 0 then -1 else 1
                    colour = borderColour + sum (map segCovered linesX)

fillPolygon : Ink -> Int -> Int -> List Segment -> IO ()
fillPolygon ink w h [] = pure ()
fillPolygon ink w h (pl::pls) = fillPolygon' ink (rangeOf w {ok=mapPreservesNonempty psne} $ map head ps) (rangeOf h {ok=mapPreservesNonempty psne} $ map (Data.Vect.index 1) ps) [] $ sortOn (Data.Vect.head . tail . fst) $ map (orient 1) (pl::pls)
    where ps : List Point
          ps = map fst (pl::pls)
          psne : NonEmpty ps
          psne = mapPreservesNonempty IsNonEmpty
          rangeOf : Int -> (l:List Double) -> {ok:NonEmpty l} -> List Int
          rangeOf lim xs = let
                  low = cast $ floor $ foldr1 min xs
                  high = cast $ ceiling $ foldr1 max xs
              in if low >= lim || high < -1 then [] else [(max (-1) low)..(min lim high)]

drawBeziers : Double -> Int -> Int -> Ink -> List (BezierPointType, Point) -> IO ()
drawBeziers s w h ink ps = fillPolygon ink w h $ thickenCurve s (fst closeAndCurve, fromList singleCurve)
    where closeAndCurve : Pair Bool (List (Bool, Point))
          closeAndCurve = map mergeCurves $ map (map (map (bezierToLines s w h))) $ segmentBeziers ps
          singleCurve = snd closeAndCurve

drawBezier : Double -> Int -> Int -> Ink -> Vect 4 Point -> IO ()
drawBezier s w h ink ps = drawBeziers s w h ink $ toList $ map (\p => (Control,p)) ps

drawLine : Double -> Int -> Int -> Ink -> Point -> Point -> IO ()
drawLine s w h ink p0 p1 = drawBeziers s w h ink [(Control,p0),(Control,p1)]

drawCircle : Double -> Int -> Int -> Ink -> Point -> Double -> IO ()
drawCircle s w h ink [cx,cy] r = for_ [(max 0 $ cast $ floor $ cy - r - weight - 0.5)..(min h $ cast $ ceiling $ cy + r + weight + 0.5)] (\y =>
        let yoff = cast y - cy
            -- The 2s here are just to be conservative about rounding.
            xOuter = cast $ sqrt $ (r+weight+2)*(r+weight+2) - yoff*yoff
            xInner = cast $ sqrt $ (r-weight-2)*(r-weight-2) - yoff*yoff
            range = \a, b => if a > w || b < 0 then [] else [(max a 0)..(min b w)]
            area = if xInner == 0 then range (cast cx-xOuter) (cast cx+xOuter) else range (cast cx-xOuter) (cast cx-xInner) ++ range (cast cx+xInner) (cast cx+xOuter)
        in for_ area (\x => renderPoint x y)
    )
    where weight : Double
          weight = lineWeight * s / 2
          renderPoint : Int -> Int -> IO ()
          renderPoint x y = let
                  r' = sqrt $ (cast x - cx)*(cast x - cx) + (cast y - cy)*(cast y-cy)
                  c = 1 - max 0 (r'-r-weight+0.5) - max 0 (r-r'-weight+0.5)
              in if c > 0 then ink x y c else pure ()

export
drawRaw : Double -> Transform -> (Int -> Int -> IO Colour) -> (Int -> Int -> Colour -> IO ()) -> Int -> Int -> SDLFont -> Picture -> IO ()
drawRaw s t read write w h font pic = if culled (transformHull t $ pictureHull pic) then pure () else case pic of
        Dot p => drawDot s ink (applyTransform t p)
        Line p p' => drawLine s w h ink (applyTransform t p) (applyTransform t p')
        Bezier ps => drawBezier s w h ink (map (applyTransform t) ps)
        Beziers ps => drawBeziers s w h ink (map (map $ applyTransform t) ps)
        Circle p r => drawCircle s w h ink (applyTransform t p) (r * scale t)
        Text text => pure ()
        Transformed t' pic' => drawRaw s (t <+> t') read write w h font pic'
        Pictures pics _ => for_ pics (drawRaw s t read write w h font)
    where decrease : Bits8 -> Double -> Bits8
          decrease b c = let c' = fromInteger $ cast (255*c) in if c' > b then 0 else b + 255*c' -- subtraction isn't allowed with Bits8s, but 255 = -1
          ink : Ink
          ink x y c = if c <= 0
              then pure () else if c >= 1
              then write x y (0,0,0) else do
                  (r,g,b) <- read x y
                  write x y (decrease r c, decrease g c, decrease b c)
          weight : Double
          weight = lineWeight * s
          culled (MkHull pts) = all (\[x,_] => x < -weight) pts || all (\[_,y] => y < -weight) pts || all (\[x,_] => x > cast w + weight) pts || all (\[_,y] => y > cast h + weight) pts
