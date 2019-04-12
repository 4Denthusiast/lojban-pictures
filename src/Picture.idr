module Picture

import Control.Algebra
import public Control.Algebra.NumericImplementations
import Data.Vect
import Debug.Trace
import Graphics.Color
import Graphics.SDL2.SDL
import Graphics.SDL2.SDLGFX
import Graphics.SDL2.SDLTTF

%access public export

-- Although this is called "Point", it's used both for vectors and elements of an affine space.
Point : Type
Point = Vect 2 Double

record Angle where
    constructor Ang
    cos : Double
    sin : Double

Eq Angle where
    (==) (Ang c s) (Ang c' s') = c == c' && s == s'

rotate : Angle -> Point -> Point
rotate (Ang c s) [x,y] = [c*x+s*y, c*y-s*x]

implementation Semigroup Angle where
    (<+>) (Ang c s) (Ang c' s') = Ang (c*c' - s*s') (c*s' + s*c')

implementation Monoid Angle where
    neutral = Ang 1 0

implementation Group Angle where
    inverse (Ang c s) = Ang c (-s)

right : Angle
right = Ang 0 1
left : Angle
left  = Ang 0 (-1)
back : Angle
back  = Ang (-1) 0

angle : Double -> Angle
angle x = Ang (cos x) (sin x)

Show Angle where
    show (Ang c s) = (++"°") $ show $ the Int $ cast $ atan2 s c / pi * 180

implementation (Semigroup a) => Semigroup (Vect n a) where
    (<+>) = liftA2 (<+>)

implementation (Monoid a) => Monoid (Vect n a) where
    neutral = pure neutral

implementation (Group a) => Group (Vect n a) where
    inverse = map inverse

record Position where
    constructor MkPosition
    pos : Point
    angle : Angle

Eq Position where
    (==) (MkPosition p a) (MkPosition p' a') = p == p' && a == a'

rotatePosition : Angle -> Position -> Position
rotatePosition da (MkPosition p a) = MkPosition (rotate da p) (da <+> a)

translatePosition : Point -> Position -> Position
translatePosition dp (MkPosition p a) = MkPosition (dp <+> p) a

Semigroup Position where
    (<+>) (MkPosition p a) p' = translatePosition p $ rotatePosition a p'

Monoid Position where
    neutral = MkPosition [0,0] neutral

Group Position where
    inverse (MkPosition p a) = MkPosition (rotate (back <-> a) p) (inverse a)

Show Position where
    showPrec d (MkPosition p a) = showCon d "MkPosition" $ showArg p ++ showArg a

record Transform where
    constructor MkTransform
    pos : Position
    scale : Double

Eq Transform where
    (==) (MkTransform p s) (MkTransform p' s') = p == p' && s == s'

scalePosition : Double -> Position -> Position
scalePosition s (MkPosition p a) = MkPosition ((s*) <$> p) a

applyTransform : Transform -> Point -> Point
applyTransform (MkTransform (MkPosition p a) s) = (<+>) p . rotate a . map (s*)

transformPosition : Transform -> Position -> Position
transformPosition (MkTransform tp s) p = tp <+> scalePosition s p

translateTransform : Point -> Transform
translateTransform [x,y] = MkTransform (MkPosition [x,y] neutral) 1

rotateTransform : Angle -> Transform
rotateTransform a = MkTransform (MkPosition neutral a) 1

scaleTransform : Double -> Transform
scaleTransform s = MkTransform neutral s

Semigroup Transform where
    (<+>) (MkTransform p s) (MkTransform p' s') = MkTransform (p <+> scalePosition s p') (s*s')

Monoid Transform where
    neutral = MkTransform neutral 1

Group Transform where
    inverse (MkTransform p s) = MkTransform (inverse $ scalePosition (1/s) p) (1/s)

data ConvexHull = MkHull (List Point)

Show ConvexHull where
    showPrec d (MkHull ps) = showCon d "MkHull" $ showArg ps

makeHull : List Point -> ConvexHull
makeHull [] = MkHull []
makeHull ps = MkHull $ reverse $ foldl addPoint [] sorted
    where pivot : Point
          pivot = foldr1 max ps
          angleTo : Point -> Point -> Double
          angleTo p p' = (\[x,y] => atan2 x y) $ p' <-> p
          cmpAngle : Point -> Point -> Ordering
          cmpAngle p p' = compare (angleTo pivot p) (angleTo pivot p')
          sorted : List Point
          sorted = sortBy cmpAngle ps
          addPoint : List Point -> Point -> List Point
          addPoint [] p = [p]
          addPoint [ep] p = [p,ep]
          addPoint (ep::pp::h) p = if angleTo pp p > angleTo pp ep then p::ep::pp::h else p::pp::h
          debug : List Point -> List Point
          debug x = trace ("Making hull of "++show ps++"\n\tPivot: "++show pivot++"\n\tSorted: "++show sorted++"\n\tFinal: "++show x) x

emptyHull : ConvexHull
emptyHull = makeHull []

hullUnion : List ConvexHull -> ConvexHull
hullUnion = makeHull . concatMap (\(MkHull ps) => ps)

transformHull : Transform -> ConvexHull -> ConvexHull
transformHull t (MkHull h) = MkHull $ map (applyTransform t) h

-- All the points p such that (p + [0,ε]) is not in the convex hull, from left to right.
upperSide : ConvexHull -> List Point
upperSide (MkHull []) = []
upperSide (MkHull [p]) = [p]
upperSide (MkHull ps) =
        map snd $
        takeWhile' ((>0) . head . fst) $
        dropWhile (\([x,y],_) => x == 0 && y > 0) $
        dropWhile (<=([0,0],[0,0])) $
        dropWhile (>([0,0],[0,0])) $
        --(\d => trace ("upperSide of "++show ps++"\n\tdiffs: "++show d) d) $
        addDiffs (ps ++ ps ++ ps)
    where addDiffs : List Point -> List (Point, Point)
          addDiffs (x::x'::xs) = (x'<->x, x) :: addDiffs (x'::xs)
          addDiffs _ = []
          takeWhile' : (e -> Bool) -> List e -> List e
          takeWhile' f (x::xs) = if f x then x :: takeWhile' f xs else [x]

lowerSide : ConvexHull -> List Point
lowerSide = reverse . map (rotate back) . upperSide . transformHull (rotateTransform back)

-- The minimum y such that (transformHull (translateTransform 0 y) h0) is entirely above h1
minShiftToDisjoint : ConvexHull -> ConvexHull -> Double
minShiftToDisjoint h0 h1 = minShift (lowerSide h0) (upperSide h1)
    where -- The vertical distance from p to (Line p0 p1)
          align : Point -> Point -> Point -> Double
          align [x0,y0] [x1,y1] [x,y] = let t = (x-x0)/(x1-x0) in y0 + t*(y1-y0) - y
          leftOf : Point -> Point -> Bool
          leftOf [x,_] [x',_] = x < x'
          gradient : Point -> Point -> Double
          gradient [x,y] [x',y'] = (y'-y) / (x'-x)
          minShift : List Point -> List Point -> Double
          minShift [] ps = -1/0
          minShift ps [] = -1/0
          minShift [p] [p'] = if leftOf p p' then (index 1 p - index 1 p') else -1/0
          minShift (p0::p1::ps) [p] =
              if (leftOf p1 p) then minShift (p1::ps) [p]
              else if (leftOf p p0) then -1/0
              else align p0 p1 p
          minShift [p'] ps = - minShift ps [p']
          minShift (p0::p1::ps) (p0'::p1'::ps') =
              if      leftOf p1 p0' then minShift (p1::ps) (p0'::p1'::ps')
              else if leftOf p1' p0 then minShift (p0::p1::ps) (p1'::ps')
              else if gradient p0 p1 >= gradient p0' p1' then (if leftOf p0 p0' then -align p0 p1 p0' else align p0' p1' p0)
              else if leftOf p0 p0'
                  then minShift (p1::ps) (p0'::p1'::ps')
                  else minShift (p0::p1::ps) (p1'::ps')

private
hypot : Double -> Double -> Double
hypot x y = sqrt $ x*x + y*y

private
diameter : Point -> Point -> (Point, Double)
diameter p p' = ((/2) <$> (p <+> p'), (\[x,y] => 0.5 * hypot x y) $ p <-> p')

private
triangleCircumcircle : Point -> Point -> Point -> (Point, Double)
triangleCircumcircle [ax,ay] [bx,by] [cx,cy] = ([px, py], hypot (ax-px) (ay-py))
    where a2 : Double
          b2 : Double
          c2 : Double
          d : Double
          px : Double
          py : Double
          a2 = ay*ay+ax*ax
          b2 = by*by+bx*bx
          c2 = cy*cy+cx*cx
          d = 2 * (ax*by + bx*cy + cx*ay - ay*bx - by*cx - cy*ax)
          px = (a2*(by-cy)+b2*(cy-ay)+c2*(ay-by))/d
          py = (a2*(cx-bx)+b2*(ax-cx)+c2*(bx-ax))/d

dot : Point -> Point -> Double
dot p p' = sum $ zipWith (*) p p'

export
circumcircle : ConvexHull -> (Point, Double)
circumcircle (MkHull []) = ([0,0],0) -- The position is arbitrary.
circumcircle (MkHull [p]) = (p,0)
circumcircle (MkHull [p,p']) = diameter p p'
circumcircle (MkHull (p0::ps')) = twoPoint p1 p2
    where ps : List Point
          ps = p0::ps'
          dist2 : Point -> Point -> Double
          dist2 p p' = sum $ map (\c => c*c) $ p <-> p'
          minBy : Ord b => List Point -> (Point -> b) -> Point
          minBy ps' f = snd $ foldr max (f p0, p0) (map (\p => (f p, p)) (ps \\ ps'))
          p1 = minBy [p0] (negate . dist2 p0)
          p2 = minBy [p0, p1] (\p => - dist2 p1 p / dot (p <-> p1) (p0 <-> p1))
          twoPoint : Point -> Point -> (Point, Double)
          twoPoint p p' = let p'' = minBy [p, p'] (\p'' => dot (p''<->p') (p''<->p) / sqrt (dist2 p'' p' * dist2 p'' p)) in
              if dot (p''<->p') (p''<->p) <= 0 then diameter p p'
              else if dot (p'<->p'') (p'<->p ) < 0 then twoPoint p'' p
              else if dot (p <->p'') (p <->p') < 0 then twoPoint p'' p'
              else triangleCircumcircle p p' p''

splitBezier : Vect n Point -> Double -> (Vect n Point, Vect n Point)
splitBezier {n=Z} [] t = ([],[])
splitBezier {n=S m} ps t = let (ps0,ps1) = splitBezier (zipWith lerp (init ps) (tail ps)) t in (head ps :: ps0, replace {P=flip Vect Point} (plusCommutative m 1) (ps1 ++ [last ps]))
    where lerp : Point -> Point -> Point
          lerp [x,y] [x',y'] = [t*x + (1-t)*x', t*y + (1-t)*y']

subdivideBezier : Vect (S n) Point -> List (Vect (S n) Point)
subdivideBezier ps = if (all (\p => dot (p <-> head ps) (p <-> last ps) <= 0) ps) then [ps] else
    let (ps0, ps1) = splitBezier ps 0.5 in subdivideBezier ps0 ++ subdivideBezier ps1

data Picture : Type where
    Dot : Point -> Picture
    Line : Point -> Point -> Picture
    Bezier : Vect 4 Point -> Picture
    Circle : Point -> Double -> Picture
    Text : String -> Picture
    Transformed : Transform -> Picture -> Picture
    Pictures : List Picture -> Picture

pictureHull : Picture -> ConvexHull
pictureHull (Dot p) = makeHull [p]
pictureHull (Line p p') = makeHull [p,p']
pictureHull (Bezier ps) = makeHull $ concat $ map toList $ subdivideBezier ps
pictureHull (Circle p r) = transformHull (MkTransform (MkPosition p neutral) (r/y)) $ makeHull $ [[1,0],[0.5,-y],[-0.5,-y],[-1,0],[-0.5,y],[0.5,y]]
    where y = sqrt 3 / 2
pictureHull (Text s) = let l = cast (length s) / 4 in makeHull [[-l,0],[0,l],[l,0],[0,-l]] -- I don't have any good estimate for text's size.
pictureHull (Transformed t p) = transformHull t $ pictureHull p
pictureHull (Pictures ps) = hullUnion $ map pictureHull ps

Semigroup Picture where
    (<+>) a b = Pictures [a,b]

blankPicture : Picture
blankPicture = Pictures []

Show Picture where
    show p = "Pict"

transformToInt : Transform -> Point -> Vect 2 Int
transformToInt t = liftA2 (*) [1,-1] . map (cast . (+0.5)) . applyTransform t

strokeLines : SDLRenderer -> List (Vect 2 Int) -> Int -> Int -> Int -> Int -> IO()
strokeLines rend ps r g b a = sequence_ $ the (List (IO ())) $ zipWith (\[x0,y0], [x1,y1] => strokeLine rend x0 y0 x1 y1 r g b a) ps (drop 1 ps)

drawBezier : Transform -> SDLRenderer -> Vect 4 Point -> IO ()
drawBezier t rend ps = let
        [xs,ys] = transpose $ map (transformToInt t) ps
    in do --strokeLines rend (toList $ map (transformToInt t) ps) 255 0 0 255
          strokeBezier rend xs ys 6 0 0 0 255

draw : Transform -> SDLRenderer -> SDLFont -> Picture -> IO ()
draw t rend font (Dot p) = let
        [x,y] = transformToInt t p
    in filledRectangle rend (x-1) (y-1) (x+1) (y+1) 0 0 0 255
draw t rend font (Line e0 e1) = let
        [x0,y0] = transformToInt t e0
        [x1,y1] = transformToInt t e1
    in strokeLine rend x0 y0 x1 y1 0 0 0 255
draw t rend font (Bezier ps) = sequence_ $ map (drawBezier t rend) (subdivideBezier ps)
draw t rend font (Circle c r) = let
        [x,y] = transformToInt t c
        r' = cast $ r * scale t
    in strokeAACircle rend x y r' 0 0 0 255
draw t rend font (Text s) = let
        [x,y] = transformToInt t [0,0]
    in renderTextSolid rend font s black x y
draw t rend font (Transformed t' p) = draw (t <+> t') rend font p
draw t rend font (Pictures ps) = traverse_ (draw t rend font) ps
