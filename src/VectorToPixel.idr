module VectorToPixel

import Picture

import Control.Algebra
import Data.Vect
import Graphics.SDL2.SDLTTF

lineWeight : Double
lineWeight = 0.05

public export
Colour : Type
Colour = (Bits8,Bits8,Bits8)

Reader : Type
Reader = Int -> Int -> IO Colour

Writer : Type
Writer = Int -> Int -> Colour -> IO ()

Ink : Type
Ink = Int -> Int -> Double -> IO ()

drawDot : Double -> Ink -> Point -> IO ()
drawDot s ink [cx,cy] = for_ [(cast $ floor $ cy - weight - 0.5)..(cast $ ceiling $ cy + weight + 0.5)] (\y =>
        for_ [(cast $ floor $ cx - weight - 0.5)..(cast $ ceiling $ cx + weight + 0.5)] (\x => renderPoint x y)
    )
    where weight : Double
          weight = lineWeight * s
          renderPoint : Int -> Int -> IO ()
          renderPoint x y = let
                  r = sqrt $ (cast x - cx)*(cast x - cx) + (cast y - cy)*(cast y-cy)
                  c = 1 - max 0 (r-weight-0.5)
              in if c > 0 then ink x y c else pure ()

drawPlainLine : Ink -> Point -> Point -> IO ()
drawPlainLine ink [x0,y0] [x1,y1] = if abs (x0 - x1) < abs (y0 - y1) then l' (flip ink) [y0,x0] [y1,x1] else l' ink [x0,y0] [x1,y1]
    where l'' : Ink -> Point -> Point -> IO ()
          l'' ink' [x,y] [x',y'] = for_ (the (List Int) [(cast x)..(cast x')]) (\cx => ink' cx (cast $ y + (y'-y)* (cast cx-x)/(x'-x)) 1)
          l' : Ink -> Point -> Point -> IO ()
          l' ink' [x,y] [x',y'] = if x < x' then l'' ink' [x,y] [x',y'] else l'' ink' [x',y'] [x,y]

segmentBeziers : List (BezierPointType, Point) -> (Bool, List (Bool, List Point))
segmentBeziers [] = (False, [])
segmentBeziers ((t0,p0)::ps0) = if t0 == Control
        then (False, segment' ((t0,p0)::ps0))
        else (True, segment' ((t0,p0)::ps0++[(Control,p0)]))
    where segment' : List (BezierPointType, Point) -> List (Bool, List Point)
          segment' [] = []
          segment' ((t1,p)::ps) = let (psl,psr) = span ((==Control).fst) ps in (t1==Corner,p::map snd (psl ++ take 1 psr))::segment' psr

bezierToLines : List Point -> List Point
bezierToLines [] = []
bezierToLines (p::ps0) = p :: splitUntil 10 (p::fromList ps0)
    where cross : Point -> Point -> Double
          cross [x,y] [x',y'] = (x*y'-y*x')/sqrt(x'*x'+y'*y')
          straightEnough : Vect (S len) Point -> Bool
          straightEnough c = let a = head c; b = last c in
              all (\p => dot (p <-> a) (p <-> a) <= dot (a <-> b) (a <-> b) && dot (p <-> a) (b <-> a) >= 0 && dot (p <-> b) (a <-> b) >= 0 && 1 >= abs (cross (p <-> a) (b <-> a))) c
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

intersections : Vect (S n) Line -> Vect (S n) (Point,Line)
intersections ls = zipWith (\l, l' => (intersection l l', l)) ls (rotate ls)

thickenCurve : {n:Nat} -> Double -> (Bool, Vect n (Bool, Point)) -> List Point
thickenCurve s (_, []) = []
thickenCurve s (_, [(b0,p0)]) = [p0]
thickenCurve s (True, [p0,p1]) = thickenCurve s (False, [p0,p1])
-- TODO: I can probably unify these latter two cases again.
thickenCurve {n=S (S n')} s (True, ps) = toList $ intersections $ flipLine closeLine :: (lines ++ (closeLine :: otherLines))
    where n : Nat
          n = S n'
          ps' : Vect (S (S n')) Point
          ps' = map snd ps
          lines : Vect n Line
          lines = map (offsetLine (lineWeight*s)) $ zipWith lineThrough (init ps') (tail ps')
          otherLines : Vect n Line
          otherLines = map (offsetLine (2*lineWeight*s) . flipLine) (reverse lines)
          closePoint : Vect n Line -> Point
          closePoint ls = intersection (head ls) (last ls)
          closeLine = lineThrough (closePoint lines) (closePoint otherLines)
thickenCurve {n=S (S n')} s (False, ps) = toList $ intersections $ map (offsetLine (lineWeight*s)) $ endCap ps' :: (lines ++ (endCap $ reverse ps') :: otherLines)
    where ps' : Vect (S (S n')) Point
          ps' = map snd ps
          lines : Vect (S n') Line
          lines = zipWith lineThrough (init ps') (tail ps')
          otherLines : Vect (S n') Line
          otherLines = map flipLine (reverse lines)
          endCap ([x,y]::[x',y']::_) = makeLine (x-x') (y-y') (x*(x-x')+y*(y-y'))

-- TODO: It would probably actually be more efficient to remove this entire step and just sort the lines individually.
verticalSegments : List (Point,Line) -> List (Point, List (Line,Point))
verticalSegments pls0 = sortBy (\([_,y],_), ([_,y'],_) => compare y y') $ oneSide True [] (reverse $ addNextPoints pls0) ++ oneSide False [] (map (\(p,l,p') => (p',l,p)) $ addNextPoints pls0)
    where addNextPoints : List (Point,Line) -> List (Point,Line,Point)
          addNextPoints [] = []
          addNextPoints ((p,l)::pls) = addNextPoints' p ((p,l)::pls) {ok=IsNonEmpty}
          addNextPoints' : Point -> l:List (Point,Line) -> {ok:NonEmpty l} -> List
          addNextPoints' p0 [(p,l)] = [(p,l,p0)]
          addNextPoints' p0 ((p,l)::(p',l')::pls) = (p,l,p') :: addNextPoints' p0 ((p',l')::pls)
          rightFacing : (Point,Line,Point) -> Bool
          rightFacing (_,MkLine x _ _,_) = x > 0
          oneSide : Bool -> List (Line,Point) -> List (Point,Line,Point) -> List (Point, List (Line,Point))
          oneSide r seg (plp::plps) | rightFacing plp == r = oneSide r (plp::seg) plps
          oneSide r ((p,l,p')::seg) plps = (p, map snd $ (p,l,p')::seg) :: oneSide r [] plps
          oneSide r [] (plp::plps) = oneSide r [] plps
          oneSide r [] [] = []

-- This assumes the (x,y) pixel covers [x,x+1]*[y,y+1], which is inconsistent with some of the other primitives.
fillPolygon' : Ink -> Double -> Double -> Double -> Double -> List (List (Line,Point)) -> List (Point, List (Line,Point)) -> IO ()
fillPolygon' ink xRange [] incoming segs = pure ()
fillPolygon' ink xRange (y0::yRange) incoming segs = fillLine 0 xRange [] lines *> fillPolygon' ink xRange yRange outgoing remainingSegs
    where (newSegs, remainingSegs) = span (\([_,y],_) => y <= (cast y0 + 1)) segs
          lineStarts = newSegs ++ mapMaybe (\inc => case inc of
                  [] => Nothing
                  ((l,p)::inc') => Just (horizontalIntersect l y0, (l,p)::inc')
              )
          followLine : (Point, List (Line, Point)) -> (Maybe (List (Line,Point)), List (Point,Line,Point))
          followLine (p,[]) = (Nothing, [])
          followLine (p,(l,[x,y])::lps) = if y > cast y0 + 1
              then (Just ((l,[x,y])::lps), [(p,l,horizontalIntersect l (cast y0 + 1))])
              else ((p,l,[x,y])::) <$> followLine ([x,y],lps)
          outgoingAndLines = map followLine lineStarts
          lines = sortBy (\([x,_],_), ([x',_],_) => compare x x') $ map (\(p,l,p') => if head p < head p' then (p,l,p') else (p',l,p)) $ concatMap snd outgoingAndLines
          outgoing = mapMaybes fst outgoingAndLines
          fillLine covered [] incomingX ls = pure ()
          fillLine covered (x0::xs) ls

fillPolygon : Ink -> List (Point,Line) -> IO ()
fillPolygon ink [] = pure ()
fillPolygon ink (pl::pls) = fillPolygon' ink (rangeOf $ map head ps) (rangeOf $ map (index 1) ps) [] $ verticalSegments (pl::pls)
    where ps = map fst (pl::pls)
          rangeOf : (l:List Double) -> {ok:NonEmpty l} -> List Int
          rangeOf xs = [(floor $ cast $ foldr1 min xs)..(ceiling $ cast $ foldr1 max xs)]

drawBeziers : Double -> Ink -> List (BezierPointType, Point) -> IO ()
drawBeziers s ink ps = fillPolygon ink $ thickenCurve s (fst closeAndCurve, fromList singleCurve)
    where closeAndCurve : Pair Bool (List (Bool, Point))
          closeAndCurve = map mergeCurves $ map (map (map bezierToLines)) $ segmentBeziers ps
          singleCurve = snd closeAndCurve

drawBezier : Double -> Ink -> Vect 4 Point -> IO ()
drawBezier s ink ps = drawBeziers s ink $ toList $ map (\p => (Control,p)) ps

drawLine : Double -> Ink -> Point -> Point -> IO ()
drawLine s ink p0 p1 = drawBeziers s ink [(Control,p0),(Control,p1)]

drawCircle : Double -> Ink -> Point -> Double -> IO ()
drawCircle s ink [cx,cy] r = for_ [(cast $ floor $ cy - r - weight - 0.5)..(cast $ ceiling $ cy + r + weight + 0.5)] (\y =>
        let yoff = cast y - cy
            -- The 2s here are just to be conservative about rounding.
            xOuter = cast $ sqrt $ (r+weight+2)*(r+weight+2) - yoff*yoff
            xInner = cast $ sqrt $ (r-weight-2)*(r-weight-2) - yoff*yoff
            area = if xInner == 0 then [(cast cx-xOuter)..(cast cx+xOuter)] else [(cast cx-xOuter)..(cast cx-xInner)] ++ [(cast cx+xInner)..(cast cx+xOuter)]
        in for_ area (\x => renderPoint x y)
    )
    where weight : Double
          weight = lineWeight * s
          renderPoint : Int -> Int -> IO ()
          renderPoint x y = let
                  r' = sqrt $ (cast x - cx)*(cast x - cx) + (cast y - cy)*(cast y-cy)
                  c = 1 - max 0 (r'-r-weight-0.5) - max 0 (r-r'-weight-0.5)
              in if c > 0 then ink x y c else pure ()

export
drawRaw : Double -> Transform -> (Int -> Int -> IO Colour) -> (Int -> Int -> Colour -> IO ()) -> Int -> Int -> SDLFont -> Picture -> IO ()
drawRaw s t read write w h font pic = if culled (transformHull t $ pictureHull pic) then pure () else case pic of
        Dot p => drawDot s ink (applyTransform t p)
        Line p p' => drawLine s ink (applyTransform t p) (applyTransform t p')
        Bezier ps => drawBezier s ink (map (applyTransform t) ps)
        Beziers ps => drawBeziers s ink (map (map $ applyTransform t) ps)
        Circle p r => drawCircle s ink (applyTransform t p) (r * scale t)
        Text text => pure ()
        Transformed t' pic' => drawRaw s (t <+> t') read write w h font pic'
        Pictures pics => for_ pics (drawRaw s t read write w h font)
    where decrease : Bits8 -> Double -> Bits8
          decrease b c = let c' = fromInteger $ cast (255*c) in if c' > b then 0 else b + 255*c' -- subtraction isn't allowed with Bits8s, but 255 = -1
          ink : Ink
          ink x y c = do
              (r,g,b) <- read x y
              write x y (decrease r c, decrease g c, decrease b c)
          culled (MkHull pts) = all (\[x,_] => x < 0) pts || all (\[_,y] => y < 0) pts || all (\[x,_] => x > cast w) pts || all (\[_,y] => y > cast h) pts
