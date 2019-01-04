module Render

import Picture
import Words
import Graph
import GraphSubstitution

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

mapWithKeys : Ord k => (k -> a -> b) -> SortedMap k a -> SortedMap k b
mapWithKeys f = fromList . map (\(k,v) => (k, f k v)) . toList

WordPicture' : Type
WordPicture' = (WordPicture, List PictureStubLabel)

stubPosition : PictureStubLabel -> WordPicture' -> Maybe Position
stubPosition s (w, ss) = stubs w ss s

maybeRevEdge : Bool -> Edge (a,a) -> Edge (a,a)
maybeRevEdge False (MkEdge n0 n1 (x,y)) = MkEdge n0 n1 (x,y)
maybeRevEdge True  (MkEdge n0 n1 (x,y)) = MkEdge n1 n0 (y,x)

absorbLeaf : NodeLabel -> SGraph PictureEdgeLabel WordPicture -> SGraph PictureEdgeLabel WordPicture
absorbLeaf nl (MkSGraph ns es) = fromMaybe (MkSGraph ns es) $ do
    (leafPic, leafStubs) <- lookup nl ns
    [(eRev, eLab)] <- the (Maybe (List (Bool,EdgeLabel))) $ case leafStubs of {[_] => Just leafStubs; _ => Nothing}
    MkEdge pl _ (pStub,lStub) <- maybeRevEdge eRev <$> lookup eLab es
    (pPic, pStubs) <- lookup pl ns
    pStubs' <- traverse (\(r,el) => (\(MkEdge _ _ (_,s)) => s) <$> maybeRevEdge r <$> lookup el es) pStubs
    let lPic = (\pPos, lPos => Transformed (MkTransform pPos 1) $ (Line [0,0] [0,2]) <+> Transformed (MkTransform (MkPosition [0,2] back <-> lPos) 1) (picture leafPic)) <$> stubs pPic pStubs' pStub <*> stubs leafPic [lStub] lStub
    pure $ case lPic of
        Just lPic' => MkSGraph (insert pl (record {picture $= (<+> lPic'), stubs $= (.(pStub::))} pPic, delete (not eRev, eLab) pStubs) $ delete nl ns) (delete eLab es)
        Nothing => MkSGraph ns (delete eLab es)

absorbLeaves : SGraph PictureEdgeLabel WordPicture -> List Picture
absorbLeaves (MkSGraph ns es) = let (MkSGraph ns' es') = foldr absorbLeaf (MkSGraph ns es) (keys ns) in
    if length (keys ns') + length (keys es') == length (keys ns) + length (keys es)
        then map (picture . fst) $ values ns'
        else absorbLeaves (MkSGraph ns' es')

combinePicturesWithoutOverlap : Picture -> Picture -> Picture
combinePicturesWithoutOverlap p0 p1 = p0 <+> Transformed t p1 
    where dy : Double
          dy = max 0 $ minShiftToDisjoint (pictureHull p0) (pictureHull p1)
          t = translateTransform 0 (-dy)

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
renderPictureGraph = renderPicture . foldr combinePicturesWithoutOverlap blankPicture . (\ps => trace ("fragments: "++show (length ps)) ps) . absorbLeaves . convertGraph
