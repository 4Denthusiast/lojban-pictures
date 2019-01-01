module Picture

import Control.Algebra
import public Control.Algebra.NumericImplementations
import Data.Vect
import Graphics.Color
import Graphics.SDL2.SDL
import Graphics.SDL2.SDLTTF

%access public export

record Angle where
    constructor Ang
    cos : Double
    sin : Double

Eq Angle where
    (==) (Ang c s) (Ang c' s') = c == c' && s == s'

rotate : Angle -> Vect 2 Double -> Vect 2 Double
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
    pos : Vect 2 Double
    angle : Angle

Eq Position where
    (==) (MkPosition p a) (MkPosition p' a') = p == p' && a == a'

rotatePosition : Angle -> Position -> Position
rotatePosition da (MkPosition p a) = MkPosition (rotate da p) (da <+> a)

translatePosition : Vect 2 Double -> Position -> Position
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

applyTransform : Transform -> Vect 2 Double -> Vect 2 Double
applyTransform (MkTransform (MkPosition p a) s) = (<+>) p . rotate a . map (s*)

translateTransform : Double -> Double -> Transform
translateTransform x y = MkTransform (MkPosition [x,y] neutral) 1

Semigroup Transform where
    (<+>) (MkTransform p s) (MkTransform p' s') = MkTransform (p <+> scalePosition s p') (s*s')

Monoid Transform where
    neutral = MkTransform neutral 1

Group Transform where
    inverse (MkTransform p s) = MkTransform (inverse $ scalePosition (1/s) p) (1/s)

data Picture : Type where
    Dot : Vect 2 Double -> Picture
    Line : Vect 2 Double -> Vect 2 Double -> Picture
    Bezier : Vect 4 (Vect 2 Double) -> Picture
    Text : String -> Picture
    Transformed : Transform -> Picture -> Picture
    Pictures : List Picture -> Picture

Semigroup Picture where
    (<+>) a b = Pictures [a,b]

blankPicture : Picture
blankPicture = Pictures []

transformToInt : Transform -> Vect 2 Double -> Vect 2 Int
transformToInt t = map cast . applyTransform t

draw : Transform -> SDLRenderer -> SDLFont -> Picture -> IO ()
draw t rend font (Dot p) = let
        [x,y] = transformToInt t p
    in sdlPixel rend x y 0 0 0 255
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
