module Picture

import Control.Algebra
import public Control.Algebra.NumericImplementations
import Data.Vect
import Graphics.Color
import Graphics.SDL2.SDL
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

translateTransform : Double -> Double -> Transform
translateTransform x y = MkTransform (MkPosition [x,y] neutral) 1

rotateTransform : Angle -> Transform
rotateTransform a = MkTransform (MkPosition neutral a) 1

Semigroup Transform where
    (<+>) (MkTransform p s) (MkTransform p' s') = MkTransform (p <+> scalePosition s p') (s*s')

Monoid Transform where
    neutral = MkTransform neutral 1

Group Transform where
    inverse (MkTransform p s) = MkTransform (inverse $ scalePosition (1/s) p) (1/s)

data ConvexHull = MkHull (List Point)

makeHull : List Point -> ConvexHull
makeHull [] = MkHull []
makeHull ps = MkHull $ foldl addPoint [] sorted
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
        addDiffs (ps ++ ps)
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

data Picture : Type where
    Dot : Point -> Picture
    Line : Point -> Point -> Picture
    Bezier : Vect 4 Point -> Picture
    Text : String -> Picture
    Transformed : Transform -> Picture -> Picture
    Pictures : List Picture -> Picture

pictureHull : Picture -> ConvexHull
pictureHull (Dot p) = makeHull [p]
pictureHull (Line p p') = makeHull [p,p']
pictureHull (Bezier ps) = makeHull $ toList ps
pictureHull (Text s) = makeHull [[0,0]] -- I don't have any good estimate for text's size.
pictureHull (Transformed t p) = transformHull t $ pictureHull p
pictureHull (Pictures ps) = hullUnion $ map pictureHull ps

Semigroup Picture where
    (<+>) a b = Pictures [a,b]

blankPicture : Picture
blankPicture = Pictures []

transformToInt : Transform -> Point -> Vect 2 Int
transformToInt t = liftA2 (*) [1,-1] . map (cast . (+0.5)) . applyTransform t

draw : Transform -> SDLRenderer -> SDLFont -> Picture -> IO ()
draw t rend font (Dot p) = let
        [x,y] = transformToInt t p
    in filledRect rend (x-1) (y-1) (x+1) (y+1) 0 0 0 255
draw t rend font (Line e0 e1) = let
        [x0,y0] = transformToInt t e0
        [x1,y1] = transformToInt t e1
    in drawLine rend x0 y0 x1 y1 0 0 0 255
draw t rend font (Bezier ps) = let
        [xs,ys] = map toList $ transpose $ map (transformToInt t) ps
    in sdlBezier rend xs ys 3 0 0 0 255
draw t rend font (Text s) = let
        [x,y] = transformToInt t [0,0]
    in renderTextSolid rend font s black x y
draw t rend font (Transformed t' p) = draw (t <+> t') rend font p
draw t rend font (Pictures ps) = traverse_ (draw t rend font) ps
