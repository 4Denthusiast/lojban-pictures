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

dot : Point -> Point -> Double
dot p p' = sum $ zipWith (*) p p'

cross : Point -> Point -> Double
cross [x,y] [x',y'] = (x*y'-y*x')

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

-- If I were using exact arithmetic, the "rightness" check would be superfluous. With floats, it prevents collinear points from appearing on the boundary in the wrong order. All the other simpler algorithms I could think of also suffer from numerical instability.
hullInterval : Nat -> Point -> Point -> List Point -> List Point
hullInterval Z _ _ = idris_crash "Ran out of time when computing a convex hull." -- I know this is impossible to reach. It's just easier to have the explicit limit so the totality checker accepts the implementaiton.
hullInterval (S t) pl pr = hullInterval' . filter ((>0) . fst) . map (\p => (cross (pr <-> pl) (p <-> pl), p))
    where hullInterval' : List (Double, Point) -> List Point
          hullInterval' [] = [pl]
          hullInterval' (p0::ps0) = let
                  pivot = snd $ foldr max p0 ps0
                  ps = map snd (p0::ps0)
                  rightness = \p => dot (p <-> pl) (pr <-> pl)
              in hullInterval t pl pivot (filter (\p => rightness p < rightness pivot) ps) ++ hullInterval t pivot pr (filter (\p => rightness p > rightness pivot) ps)

makeHull : List Point -> ConvexHull
makeHull [] = MkHull []
makeHull [p] = MkHull [p]
makeHull (p0::ps0) = MkHull $ hullInterval (Prelude.List.length ps) leftPoint rightPoint ps ++ hullInterval (Prelude.List.length ps) rightPoint leftPoint ps
    where ps : List Point
          ps = p0::ps0
          leftPoint = foldr max p0 ps0
          rightPoint = foldr min p0 ps0

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

public export
data BezierPointType = Control | Smooth | Corner

implementation Eq BezierPointType where
    Control == Control = True
    Smooth == Smooth = True
    Corner == Corner = True
    _ == _ = False

data Picture : Type where
    Dot : Point -> Picture
    Line : Point -> Point -> Picture
    Bezier : Vect 4 Point -> Picture -- deprecated
    Beziers : List (BezierPointType, Point) -> Picture
    Circle : Point -> Double -> Picture
    Text : String -> Picture
    Transformed : Transform -> Picture -> Picture
    Pictures : List Picture -> ConvexHull -> Picture

pictureHull : Picture -> ConvexHull
pictureHull (Dot p) = makeHull [p]
pictureHull (Line p p') = makeHull [p,p']
pictureHull (Bezier ps) = makeHull $ toList ps
pictureHull (Beziers ps) = makeHull $ map snd ps
pictureHull (Circle p r) = transformHull (MkTransform (MkPosition p neutral) (r/y)) $ makeHull $ [[1,0],[0.5,-y],[-0.5,-y],[-1,0],[-0.5,y],[0.5,y]]
    where y = sqrt 3 / 2
pictureHull (Text s) = let l = cast (length s) / 4 in makeHull [[-l,0],[0,l],[l,0],[0,-l]] -- I don't have any good estimate for text's size.
pictureHull (Transformed t p) = transformHull t $ pictureHull p
pictureHull (Pictures ps h) = h

public export
pictures : List Picture -> Picture
pictures ps = Pictures ps (hullUnion $ map pictureHull ps)

Semigroup Picture where
    (<+>) a b = pictures [a,b]

blankPicture : Picture
blankPicture = pictures []

Show Picture where
    show p = "Pict"

transformToInt : Transform -> Point -> Vect 2 Int
transformToInt t = liftA2 (*) [1,-1] . map (cast . (+0.5)) . applyTransform t

draw : Transform -> SDLRenderer -> SDLFont -> Picture -> IO ()
draw t rend font (Dot p) = let
        [x,y] = transformToInt t p
    in filledRectangle rend (x-1) (y-1) (x+1) (y+1) 0 0 0 255
draw t rend font (Line e0 e1) = let
        [x0,y0] = transformToInt t e0
        [x1,y1] = transformToInt t e1
    in strokeLine rend x0 y0 x1 y1 0 0 0 255
draw t rend font (Bezier ps) = let
        [xs,ys] = transpose $ map (transformToInt t) ps
    in strokeBezier rend xs ys 6 0 0 0 255
draw t rend font (Circle c r) = let
        [x,y] = transformToInt t c
        r' = cast $ r * scale t
    in strokeAACircle rend x y r' 0 0 0 255
draw t rend font (Text s) = let
        [x,y] = transformToInt t [0,0]
    in renderTextSolid rend font s black x y
draw t rend font (Transformed t' p) = draw (t <+> t') rend font p
draw t rend font (Pictures ps h) = traverse_ (draw t rend font) ps
