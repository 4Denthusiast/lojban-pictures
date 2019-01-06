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

maybeReverse : Reversable e => Bool -> e -> e
maybeReverse False = id
maybeReverse True  = reverse

nearStub : (Bool, Edge PictureEdgeLabel) -> PictureStubLabel
nearStub = fst . edgeData . uncurry maybeReverse

ProcessedWord : Type
ProcessedWord = (Picture, SortedMap (NodeLabel, PictureStubLabel) Position)

EitherWord : Type
EitherWord = Either WordPicture ProcessedWord

combinePicturesWithoutOverlap : ProcessedWord -> ProcessedWord -> ProcessedWord
combinePicturesWithoutOverlap (p0,ss0) (p1,ss1) = (p0 <+> Transformed t p1, mergeLeft ss0 (map (transformPosition t) ss1))
    where dy : Double
          dy = max 0 $ minShiftToDisjoint (pictureHull p0) (pictureHull p1)
          t = translateTransform [0,-dy]

preProcessGraph : SGraph PictureEdgeLabel WordPicture -> SGraph (Edge PictureEdgeLabel) EitherWord
preProcessGraph (MkSGraph ns es) = MkSGraph (map (\(n,els) => (Left n, els)) ns) (map (\(MkEdge n0 n1 e) => MkEdge n0 n1 (MkEdge n0 n1 e)) es)

absorbLeaf : NodeLabel -> SGraph (Edge PictureEdgeLabel) ProcessedWord -> SGraph (Edge PictureEdgeLabel) ProcessedWord
absorbLeaf nl g = fromMaybe g $ do
    ((lPic, lStubs), lEdges) <- lookup nl $ nodeMap g
    [(eRev, el)] <- the (Maybe (List (Bool,EdgeLabel))) $ case lEdges of {[_] => Just lEdges; _ => Nothing}
    MkEdge pl _ (MkEdge pl' ll' (pStub, lStub)) <- maybeReverse eRev <$> lookup el (edgeMap g)
    ((pPic, pStubs), pEdges) <- lookup pl $ nodeMap g
    pure $ case (lookup (pl',pStub) pStubs, lookup (ll',lStub) lStubs) of
        (Just pStubPos, Just lStubPos) => let
                t = MkTransform (pStubPos <+> MkPosition [0,2] back <-> lStubPos) 1
                pic = pPic <+> Transformed t lPic <+> Transformed (MkTransform pStubPos 1) (Line [0,0] [0,2])
                stubs = pStubs <+> map (transformPosition t) lStubs
            in record {nodeMap $= insert pl ((pic, stubs), filter ((/=el).snd) pEdges) . delete nl, edgeMap $= delete el} g
        _ => record {edgeMap $= delete el} g
    
absorbLeaves : SGraph (Edge PictureEdgeLabel) ProcessedWord -> SGraph (Edge PictureEdgeLabel) ProcessedWord
absorbLeaves g = let g' = foldr absorbLeaf g (keys $ nodeMap g) in
    if length (keys $ edgeMap g') == length (keys $ edgeMap g)
        then g'
        else absorbLeaves g'

mutual
    processInside : NodeLabel -> SGraph (Edge PictureEdgeLabel) EitherWord -> SGraph (Edge PictureEdgeLabel) EitherWord
    processInside nl g = fromMaybe g $ do
        (n,els) <- lookup nl $ nodeMap g
        w <- either Just (const Nothing) n
        let es = map (uncurry maybeReverse) $ catMaybes $ map (\(r,el) => (\e => (r,e)) <$> lookup el (edgeMap g)) els
        let insideLabels = map (\(MkEdge _ l _) => l) $ filter ((==Around) . Basics.fst . edgeData . edgeData) es
        let (gi, ies, g') = cutGraph insideLabels g
        (_,els') <- lookup nl $ nodeMap g'
        let (iPic, iStubs) = processGraph gi
        let w' = w $ MkWordContext (pictureHull iPic) emptyHull (map (fst . edgeData . edgeData) es)
        let wStubs = the (SortedMap (NodeLabel, PictureStubLabel) Position) $ fromList $ catMaybes $ map ((\s => (\p => ((nl,s),p)) <$> stubs w' s) . fst . edgeData . edgeData) es
        let wProc = case stubs w' Around of
            Nothing => (picture w', wStubs)
            Just p => (picture w' <+> Transformed (MkTransform p 1) iPic, mergeLeft wStubs $ map (p<+>) iStubs)
        let ies' = map (\(MkEdge n0 _ e) => MkEdge n0 nl e) ies
        pure $ record {nodeMap $= insert nl (Right wProc, els' ++ map (\e => (False, e)) (keys ies')), edgeMap $= mergeLeft ies'} g'
    
    processInsides : SGraph (Edge PictureEdgeLabel) EitherWord -> SGraph (Edge PictureEdgeLabel) ProcessedWord
    processInsides g = assumeProcessed $ foldr processInside g (keys $ nodeMap g)
        where assumeProcessed : SGraph (Edge PictureEdgeLabel) EitherWord -> SGraph (Edge PictureEdgeLabel) ProcessedWord
              assumeProcessed = map (\(Right n) => n)
    
    -- after absorbing all the leaves, give up on the remaining connections and combine into one picture.
    unifyPicture : SGraph (Edge PictureEdgeLabel) ProcessedWord -> ProcessedWord
    unifyPicture (MkSGraph ns _) = foldr combinePicturesWithoutOverlap (blankPicture, empty) $ map fst $ values ns
    
    processGraph : SGraph (Edge PictureEdgeLabel) EitherWord -> ProcessedWord
    processGraph = unifyPicture . absorbLeaves . processInsides

record DisplayState where
    constructor MkState
    transform : Transform
    mousePos : Point

Eq DisplayState where
    (==) (MkState t p) (MkState t' p') = t == t' && p == p'

renderPicture : Picture -> IO ()
renderPicture p = do
        (ctx, rend) <- startSDL "Pretty lojban" 600 600
        font <- ttfOpenFont "/usr/share/fonts/truetype/freefont/FreeSans.ttf" 15
        loop rend font True (MkState (MkTransform (MkPosition [300,300] neutral) 20) [0,0])
        ttfCloseFont font
        endSDL ctx rend
    where updateState : DisplayState -> Event -> DisplayState
          updateState s (MouseMotion x y x' y') = record {mousePos = [cast x, 600-cast y]} s
          updateState s (MouseWheel n) = record {transform $= (<+>) (translateTransform (mousePos s) <+> scaleTransform (exp $ cast n * 0.2) <-> translateTransform (mousePos s))} s
          updateState s _ = s
          pollEvents : Maybe Event -> IO (List Event)
          pollEvents Nothing = pure []
          pollEvents (Just ev) = map (ev ::) $ pollEvent >>= pollEvents
          loop : SDLRenderer -> SDLFont -> Bool -> DisplayState -> IO ()
          loop rend font refresh s = do
              if refresh then do
                  sdlSetRenderDrawColor rend 255 255 255 255
                  sdlRenderClear rend
                  draw (translateTransform [0,-600] <+> transform s) rend font p
                  renderPresent rend
              else pure ()
              ev0 <- waitEvent
              evs <- pollEvents ev0
              if elem AppQuit evs then pure () else
              let s' = foldl updateState s evs in
              loop rend font (s' /= s) s'

export
renderPictureGraph : PictureGraph 0 -> IO ()
renderPictureGraph = renderPicture . fst . processGraph . preProcessGraph . convertGraph
