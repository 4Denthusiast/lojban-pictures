module Render

import Words
import Graph

import Control.Algebra
import Data.SortedMap
import Data.Vect
import Debug.Trace
import Graphics.Color
import Graphics.SDL2.SDL
import Graphics.SDL2.SDLTTF

waitToClose : IO ()
waitToClose = case !waitEvent of
                  Just AppQuit => pure ()
                  ev           => waitToClose

mapAccumL : (a -> b -> (a, c)) -> a -> List b -> (List c, a)
mapAccumL f x [] = ([], x)
mapAccumL f x (y::ys) = let (x', z) = f x y in let (zs, x'') = mapAccumL f x' ys in (z::zs, x'')

adjust : (a -> a) -> k -> SortedMap k a -> SortedMap k a
adjust f k m = case lookup k m of
    Nothing => m
    Just v  => insert k (f v) m

mapWithKeys : Ord k => (k -> a -> b) -> SortedMap k a -> SortedMap k b
mapWithKeys f = fromList . map (\(k,v) => (k, f k v)) . toList

WordPicture' : Type
WordPicture' = (WordPicture, List PictureStubLabel)

stubPosition : PictureStubLabel -> WordPicture' -> Maybe Position
stubPosition s (w, ss) = stubs w ss s

annotatePictureGraph :
    Graph 0 PictureStubLabel PictureEdgeLabel WordPicture ->
    Graph 0 PictureStubLabel PictureEdgeLabel WordPicture'
annotatePictureGraph (MkGraph [] ns es) = MkGraph [] (foldr annotate (map (\n => (n,[])) ns) es) es
    where annotate' : NodeLabel -> PictureStubLabel -> SortedMap NodeLabel WordPicture' -> SortedMap NodeLabel WordPicture'
          annotate' l s ns' = adjust (\(n,ss) => (n,s::ss)) l ns'
          annotate (MkEdge n0 n1 s0 s1 _) ns' = annotate' n0 s0 $ annotate' n1 s1 ns'

arrangePictureGraph : Graph 0 PictureStubLabel PictureEdgeLabel WordPicture' -> Graph 0 PictureStubLabel PictureEdgeLabel (WordPicture', Vect 2 Double, Angle)
arrangePictureGraph (MkGraph [] ns es) = MkGraph [] (map snd $ foldr alignEdge ns'0 es) es
    where ns'0 = mapWithKeys (\l, n => (l, n, [0,0], neutral)) ns
          alignEdge : Edge PictureStubLabel PictureEdgeLabel ->
              SortedMap NodeLabel (NodeLabel, WordPicture', Vect 2 Double, Angle) ->
              SortedMap NodeLabel (NodeLabel, WordPicture', Vect 2 Double, Angle)
          alignEdge (MkEdge nl0 nl1 s0 s1 e) ns' =
              trace ("nodes: "++show ns') $
              trace ("aligning "++show (MkEdge nl0 nl1 s0 s1 e)) $
              let [Just (r0, n0, p0, a0), Just (r1, n1, p1, a1)] = map {f=Vect 2} (flip lookup ns') [nl0, nl1] in
              --trace ("currently "++show nl0++"ϵ"++show r0++", "++show nl1++"ϵ"++show r1) $
              case (stubPosition s0 n0, stubPosition s1 n1, r0 == r1) of
                  (Just sp0, Just sp1, False) =>
                      let da = angle sp0 <+> a0 <-> angle sp1 <-> a1 <+> back
                          dp = rotate a0 (pos sp0 <+> rotate (angle sp0) [0,2]) <+> p0 <-> rotate da (rotate a1 (pos sp1) <+> p1)
                      in map (\n' => if fst n' /= r1 then n' else case n' of (_, n2, p2, a2) => (r0, n2, rotate da p2 <+> dp, a2 <+> da)) ns'
                  f => trace ("alignment failed: " <+> show f) ns'

transform : Double -> Int
transform x = cast $ 300 + 20 * x

drawNode : SDLRenderer -> SDLFont -> WordPicture' -> Vect 2 Double -> Angle -> IO ()
drawNode rend font (w,ss) [x,y] a = renderTextSolid rend font (string w) black (transform x) (transform y - 7)

drawLink : SDLRenderer -> SDLFont -> Maybe Position -> Maybe Position -> PictureStubLabel -> PictureStubLabel -> IO ()
drawLink rend font (Just (MkPosition [x0,y0] a0)) (Just (MkPosition [x1,y1] a1)) s0 s1 = drawLine rend (transform x0) (transform y0) (transform x1) (transform y1) 0 0 0 255
drawLink _ _ _ _ _ _ = pure ()

export
renderPicture : PictureGraph i -> IO ()
renderPicture gr = do
        putStrLn ("parsed as: "++show gr2)
        (ctx, rend) <- startSDL "Pretty lojban" 600 600
        sdlSetRenderDrawColor rend 255 255 255 255
        sdlRenderClear rend
        font <- ttfOpenFont "/usr/share/fonts/truetype/freefont/FreeSans.ttf" 15
        traverse_ {b=Unit} (\(w,p,a) => drawNode rend font w p a) $ values $ graphNodes gr2
        traverse_ {b=Unit} (\(MkEdge n0 n1 s0 s1 e) => drawLink rend font (findStubPos n0 s0) (findStubPos n1 s1) s0 s1) $ graphEdges gr2
        renderPresent rend
        waitToClose
        ttfCloseFont font
        endSDL ctx rend
    where gr1 : Graph 0 PictureStubLabel PictureEdgeLabel WordPicture'
          gr1 = annotatePictureGraph $ permuteRoots (const []) gr
          gr2 : Graph 0 PictureStubLabel PictureEdgeLabel (WordPicture', Vect 2 Double, Angle)
          gr2 = arrangePictureGraph gr1
          findStubPos : NodeLabel -> PictureStubLabel -> Maybe Position
          findStubPos l s = do
              (w, p, a) <- SortedMap.lookup l $ graphNodes gr2
              sp0 <- stubPosition s w
              pure $ translatePosition p $ rotatePosition a $ sp0
