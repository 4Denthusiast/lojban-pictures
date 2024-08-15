module VectorToPixel

import Picture

import Control.Algebra
import Data.Vect
import Graphics.SDL2.SDLTTF

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
drawDot s ink [x,y] = ink (cast x) (cast y) 1

drawLine : Double -> Ink -> Point -> Point -> IO ()
drawLine s ink [x0,y0] [x1,y1] = if abs (x0 - x1) < abs (y0 - y1) then l' (flip ink) [y0,x0] [y1,x1] else l' ink [x0,y0] [x1,y1]
    where l'' : Ink -> Point -> Point -> IO ()
          l'' ink' [x,y] [x',y'] = for_ (the (List Int) [(cast x)..(cast x')]) (\cx => ink' cx (cast $ y + (y'-y)* (cast cx-x)/(x'-x)) 1)
          l' : Ink -> Point -> Point -> IO ()
          l' ink' [x,y] [x',y'] = if x < x' then l'' ink' [x,y] [x',y'] else l'' ink' [x',y'] [x,y]

drawBezier : Double -> Ink -> Vect 4 Point -> IO ()
drawBezier s ink ps = splitUntil 10 ps
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
          splitUntil : Nat -> Vect (S n) Point -> IO ()
          splitUntil Z ps = drawLine s ink (head ps) (last ps)
          splitUntil (S t) ps =  if straightEnough ps then splitUntil 0 ps else splitUntil t (firstHalf ps) *> splitUntil t (secondHalf ps)

drawCircle : Double -> Ink -> Point -> Double -> IO ()
drawCircle s ink [cx,cy] r = drawSide ink cx cy *> drawSide (flip ink) cy cx
    where drawSide : Ink -> Double -> Double -> IO ()
          drawSide ink' cx' cy' = for_ [(cast (cx' - r))..(cast (cx' + r))] (\ix =>
              let xoff = cast ix - cx'
                  y = sqrt (r*r-xoff*xoff)
              in ink' ix (cast $ cy' + y) 1 *> ink' ix (cast $ cy' - y) 1
          )

export
drawRaw : Double -> Transform -> (Int -> Int -> IO Colour) -> (Int -> Int -> Colour -> IO ()) -> Int -> Int -> SDLFont -> Picture -> IO ()
drawRaw s t read write w h font pic = if culled (transformHull t $ pictureHull pic) then pure () else case pic of
        Dot p => drawDot s ink (applyTransform t p)
        Line p p' => drawLine s ink (applyTransform t p) (applyTransform t p')
        Bezier ps => drawBezier s ink (map (applyTransform t) ps)
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
