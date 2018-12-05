module Main

import Parser

import Graphics.Color
import Graphics.SDL2.SDL

waitToClose : IO ()
waitToClose = case !waitEvent of
                  Just AppQuit => pure ()
                  ev           => do putStrLn (show ev)
                                     waitToClose

main : IO ()
main = do putStrLn "1"
          (ctx, rend) <- startSDL "Pretty lojban" 400 400
          putStrLn "2"
          sdlSetRenderDrawColor rend 255 255 255 255
          sdlRenderClear rend
          filledPolygon rend [10,390,390,10] [10,10,390,390] 0 0 0 255
          renderPresent rend
          waitToClose
          putStrLn "3"
          quit
