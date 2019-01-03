module Render

import Picture
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
    Graph 0 PictureEdgeLabel WordPicture ->
    Graph 0 PictureEdgeLabel WordPicture'
annotatePictureGraph (MkGraph [] ns es) = MkGraph [] (foldr annotate (map (\n => (n,[])) ns) es) es
    where annotate' : NodeLabel -> PictureStubLabel -> SortedMap NodeLabel WordPicture' -> SortedMap NodeLabel WordPicture'
          annotate' l s ns' = adjust (\(n,ss) => (n,s::ss)) l ns'
          annotate (MkEdge n0 n1 (s0,s1)) ns' = annotate' n0 s0 $ annotate' n1 s1 ns'

arrangePictureGraph : Graph 0 PictureEdgeLabel WordPicture' -> Graph 0 PictureEdgeLabel (WordPicture', Position)
arrangePictureGraph (MkGraph [] ns es) = MkGraph [] (map snd $ foldr alignEdge ns'0 es) es
    where ns'0 = mapWithKeys (\l, n => (l, n, neutral)) ns
          alignEdge : Edge PictureEdgeLabel ->
              SortedMap NodeLabel (NodeLabel, WordPicture', Position) ->
              SortedMap NodeLabel (NodeLabel, WordPicture', Position)
          alignEdge (MkEdge nl0 nl1 (s0,s1)) ns' =
              --trace ("nodes: "++show ns') $
              --trace ("aligning "++show (MkEdge nl0 nl1 s0 s1 e)) $
              let [Just (r0, n0, p0), Just (r1, n1, p1)] = map {f=Vect 2} (flip lookup ns') [nl0, nl1] in
              --trace ("currently "++show nl0++"ϵ"++show r0++", "++show nl1++"ϵ"++show r1) $
              case (stubPosition s0 n0, stubPosition s1 n1, r0 == r1) of
                  (Just sp0, Just sp1, False) =>
                      let dp = p0 <+> sp0 <+> (MkPosition [0,2] back) <-> sp1 <-> p1
                      in map (\n' => if fst n' /= r1 then n' else case n' of (_, n2, p2) => (r0, n2, dp <+> p2)) ns'
                  f => ns' --trace ("alignment failed: " <+> show f) ns'

drawLink : Maybe Position -> Maybe Position -> PictureStubLabel -> PictureStubLabel -> Picture
drawLink (Just (MkPosition p0 a0)) (Just (MkPosition p1 a1)) s0 s1 = Line p0 p1
drawLink _ _ _ _ = blankPicture

graphToPicture : Graph 0 PictureEdgeLabel (WordPicture', Position) -> Picture
graphToPicture gr = Pictures $ map (\(w, p) => Transformed (MkTransform p 1) $ picture (fst w)) (values $ graphNodes gr) ++ map (\(MkEdge n0 n1 (s0,s1)) => drawLink (findStubPos n0 s0) (findStubPos n1 s1) s0 s1) (graphEdges gr)
    where findStubPos : NodeLabel -> PictureStubLabel -> Maybe Position
          findStubPos l s = do
              (w, p) <- SortedMap.lookup l $ graphNodes gr
              sp0 <- stubPosition s w
              pure $ p <+> sp0

renderPicture : Picture -> IO ()
renderPicture p = do
        (ctx, rend) <- startSDL "Pretty lojban" 600 600
        font <- ttfOpenFont "/usr/share/fonts/truetype/freefont/FreeSans.ttf" 15
        loop rend font True (MkTransform (MkPosition [300,-300] neutral) 20)
        ttfCloseFont font
        endSDL ctx rend
    where updateState : Transform -> Event -> Transform
          updateState t (MouseMotion x y x' y') = translateTransform (cast x') (cast y') <+> t -- There's clearly some bug in the language here. I have to have the (pure (x,y)), or else x' and y' end up with the values of x and y instead.
          updateState t _ = t
          pollEvents : Maybe Event -> IO (List Event)
          pollEvents Nothing = pure []
          pollEvents (Just ev) = map (ev ::) $ pollEvent >>= pollEvents
          loop : SDLRenderer -> SDLFont -> Bool -> Transform -> IO ()
          loop rend font refresh t = do
              if refresh then do
                  sdlSetRenderDrawColor rend 255 255 255 255
                  sdlRenderClear rend
                  draw t rend font p
                  renderPresent rend
              else pure ()
              ev0 <- waitEvent
              evs <- pollEvents ev0
              if elem AppQuit evs then pure () else
              let t' = foldl updateState t evs in
              loop rend font (t' /= t) t'

export
renderPictureGraph : PictureGraph 0 -> IO ()
renderPictureGraph = renderPicture . graphToPicture . arrangePictureGraph . annotatePictureGraph
