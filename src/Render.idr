module Render

import Picture
import Words
import Graph
import GraphSubstitution
import VectorToPixel

import Control.Algebra
import Data.SortedMap
import Data.SortedSet
import Data.Vect
import Debug.Trace
import Graphics.Color
import Graphics.SDL2.SDL
import Graphics.SDL2.SDLTTF

ProcessedWord : Type
ProcessedWord = (Picture, SortedMap (NodeLabel, PictureStubLabel) Position)

EitherWord : Type
EitherWord = Either WordPicture ProcessedWord

combinePicturesWithoutOverlap : ProcessedWord -> ProcessedWord -> ProcessedWord
combinePicturesWithoutOverlap (p0,ss0) (p1,ss1) = (p0 <+> Transformed t p1, mergeLeft ss0 (map (transformPosition t) ss1))
    where dy : Double
          dy = max 0 $ minShiftToDisjoint (pictureHull p0) (pictureHull p1)
          t = translateTransform [0,-1-dy]

rerouteAtNode : NodeLabel -> SGraph PictureEdgeLabel WordPicture -> SGraph PictureEdgeLabel WordPicture
rerouteAtNode nl g = fromMaybe g $ do
    es <- map snd <$> getAdjEdges' g nl
    guard (any (\((s,_,_),_) => case s of {Reroute _ => True; RerouteAny => True; _ => False}) es)
    let (es1,rrs) = the (List (PictureEdgeLabel,NodeLabel), List (PictureStubLabel, (PictureStubLabel, NodeLabel))) $ partitionEithers $ (\((ns,f,fs),nl') => case ns of {Reroute s => Right (s,fs,nl'); _ => Left ((ns,f,fs),nl')}) <$> es
    let rrs' = the (SortedMap PictureStubLabel (PictureStubLabel, NodeLabel)) $ fromList rrs
    let (es2,newEdges0) = the (List (PictureEdgeLabel,NodeLabel),List (Edge PictureEdgeLabel)) $ partitionEithers $ (\((ns,f,fs),nl') => case (SortedMap.lookup ns rrs') of
            Just (fs',nl'') => Right (MkEdge nl' nl'' (fs,f,fs'))
            Nothing => Left ((ns,f,fs),nl')
        ) <$> es1
    let anyBackNodes = map Basics.snd $ filter (\((_,_,fs),_) => fs == RerouteAny) es2
    anyBackNodes' <- for anyBackNodes (\nl' =>
            (\ss => (nl',ss)) <$>
            the (SortedSet PictureStubLabel) <$> fromList <$>
            catMaybes <$>
            map (\s => case s of {Reroute s' => Just s'; _ => Nothing}) <$>
            map (\(_,(s,_,_),_) => s) <$>
            getAdjEdges' g nl'
        )
    let newEdges1 = the (List (Edge PictureEdgeLabel)) $ catMaybes $ (\(s,fs,nl), (nl',ss) => if contains s ss then Nothing else Just (MkEdge nl' nl (Reroute s,False,fs))) <$> rrs <*> anyBackNodes'
    let (es3, anyForwardNodes) = the (List (PictureEdgeLabel,NodeLabel),List NodeLabel) $ map (map Basics.snd) $ partition (\((s,_,_),_) => s /= RerouteAny) es2
    let newEdges2 = case anyForwardNodes of
        [] => []
        (nl'::_) => map (\((ns,f,fs),nl'') => MkEdge nl' nl'' (ns,f,fs)) es3
    pure $ foldl addEdge (deleteNode g nl) (newEdges0 ++ newEdges1 ++ newEdges2)

applyReroutes : SGraph PictureEdgeLabel WordPicture -> SGraph PictureEdgeLabel WordPicture
applyReroutes g = foldr rerouteAtNode g (keys $ nodeMap g)

preProcessGraph : SGraph PictureEdgeLabel WordPicture -> SGraph (Edge PictureEdgeLabel) EitherWord
preProcessGraph (MkSGraph ns es) = MkSGraph (map (\(n,els) => (Left n, els)) ns) (map (\(MkEdge n0 n1 e) => MkEdge n0 n1 (MkEdge n0 n1 e)) es)

absorbLeaf : NodeLabel -> SGraph (Edge PictureEdgeLabel) ProcessedWord -> SGraph (Edge PictureEdgeLabel) ProcessedWord
absorbLeaf nl0 g = fromMaybe g $ do
    (bPic, bStubs) <- getNode g nl0
    es <- getAdjEdges' g nl0
    esl <- the (Maybe $ List (Bool, Edge PictureEdgeLabel, NodeLabel)) $ for es (\(el,e,nl1) => (\b => (b,e,nl1)) <$> (/=1) <$> length <$> getAdjEdges g nl1)
    let (esh, es') = map (map Basics.snd) $ partition fst esl
    guard (length esh <= 1)
    pics <- for es' (\(MkEdge nl0' nl1' (s0,f,s1),nl1) => do
            (lPic, lStubs) <- getNode g nl1
            bs <- lookup (nl0', s0) bStubs
            ls <- lookup (nl1', s1) lStubs
            pure $ Transformed (MkTransform bs 1) $ if f
                then Transformed (MkTransform (MkPosition [0,0] back <-> ls) 1) lPic
                else Line [0,0] [0,2] <+> Transformed (MkTransform (MkPosition [0,2] back <-> ls) 1) lPic
        )
    let g' = foldr (\(_,nl1), g0 => deleteNode g0 nl1) g es'
    pure $ setNode g' nl0 (bPic <+> Pictures pics, bStubs)
    
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
        let insidenessEdgeLabels = map snd $ filter (\(r,e) => (==Just Around) $ map (fst . edgeData . edgeData . maybeReverse r) $ lookup e $ edgeMap g) els
        let insideLabels = map (\(MkEdge _ l _) => l) $ filter ((==Around) . Basics.fst . edgeData . edgeData) es
        let (gi, ies, g') = cutGraph insideLabels g
        (_,els') <- lookup nl $ nodeMap g'
        let (iPic, iStubs) = processGraph gi
        let wStubList = map (fst . edgeData . edgeData) es
        let w' = w $ MkWordContext (pictureHull iPic) emptyHull wStubList
        let wStubs = the (SortedMap (NodeLabel, PictureStubLabel) Position) $ fromList $ catMaybes $ map (\s => (\p => ((nl,s),p)) <$> stubs w' s) wStubList
        let wProc = case stubs w' Around of
            Nothing => (picture w', wStubs)
            Just p => (picture w' <+> Transformed (MkTransform p 1) iPic, mergeLeft wStubs $ map (p<+>) iStubs)
        let ies' = map (\(MkEdge n0 _ e) => MkEdge n0 nl e) ies
        pure $ record {nodeMap $= insert nl (Right wProc, filter (not . (flip elem insidenessEdgeLabels) . snd) $ els' ++ map (\e => (True, e)) (keys ies')), edgeMap $= mergeLeft $ foldr delete ies' insidenessEdgeLabels} g'
    
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
    texture : (SDLTexture,(Int,Int))

-- A transform so that the picture fits within the unit circle (with a margin)
normalisePlacementTransform : Picture -> Transform
normalisePlacementTransform p = let (c, r) = circumcircle $ pictureHull p
    in scaleTransform (1/(r+1)) <+> translateTransform (inverse c)

address : Int -> Int -> Int -> Int -> Maybe Int
address w h x y = if x >= 0 && x < w && y >= 0 && y < h then Just (4*(x+w*y)) else Nothing

writeRawTex : Ptr -> Int -> Int -> Int -> Int -> (Bits8,Bits8,Bits8) -> IO ()
writeRawTex txp w h x y (r,g,b) = case address w h x y of
    Nothing => pure ()
    Just i => do
        prim_poke8 txp (i+2) r
        prim_poke8 txp (i+1) g
        prim_poke8 txp (i+0) b
        pure ()

readRawTex : Ptr -> Int -> Int -> Int -> Int -> IO (Bits8,Bits8,Bits8)
readRawTex txp w h x y = case address w h x y of
    Nothing => pure (0,0,0)
    Just i => do
        r <- prim_peek8 txp (i+2)
        g <- prim_peek8 txp (i+1)
        b <- prim_peek8 txp (i+0)
        pure (r,g,b)

renderPicture : Picture -> IO ()
renderPicture p = do
        (window, rend) <- startSDL "Pretty lojban" 600 600 [SDL_WINDOW_RESIZABLE]
        font <- ttfOpenFont "/usr/share/fonts/truetype/freefont/FreeSans.ttf" 15
        tx <- makeTexture window rend
        loop window rend font True (MkState (MkTransform (MkPosition [300,300] neutral) 300 <+> normalisePlacementTransform p) [0,0] tx)
        ttfCloseFont font
        endSDL window rend
    where makeTexture : SDLWindow -> SDLRenderer -> IO (SDLTexture,(Int,Int))
          makeTexture window rend = do
              (w,h) <- getWindowSize window
              tx <- sdlCreateTexture rend SDL_PIXELFORMAT_RGB888 SDL_TEXTUREACCESS_STREAMING w h
              pure (tx,(w,h))
          updateState : SDLWindow -> SDLRenderer -> (Bool, DisplayState) -> Event -> IO (Bool, DisplayState)
          updateState _ _ (d,s) (MouseMotion x y x' y') = pure (d, record {mousePos = [cast x, cast y]} s)
          updateState _ _ (d,s) (MouseWheel n) = pure (True, record {transform $= (<+>) (translateTransform (mousePos s) <+> scaleTransform (exp $ cast n * 0.2) <-> translateTransform (mousePos s))} s)
          updateState w r (d,s) (Resize _ _) = do
              sdlDestroyTexture $ fst $ texture s
              tx <- makeTexture w r
              pure (True, record {texture = tx} s)
          updateState _ _ s _ = pure s
          pollEvents : Maybe Event -> IO (List Event)
          pollEvents Nothing = pure []
          pollEvents (Just ev) = map (ev ::) $ pollEvent >>= pollEvents
          loop : SDLWindow -> SDLRenderer -> SDLFont -> Bool -> DisplayState -> IO ()
          loop window rend font refresh s = do
              if refresh then do
                  (MkTextureRaw txp pitch) <- lockTexture $ fst $ texture s
                  let (w,h) = snd $ texture s
                  for_ [0..(w-1)] (\x => for_ [0..(h-1)] (\y => writeRawTex txp w h x y (255,255,255)))
                  -- Consider writing everything to a Data.IOArray first. It might be more efficient.
                  --drawRaw 1 neutral (readRawTex txp w h) (writeRawTex txp w h) w h font (Bezier [[10,10],[10,590],[590,590],[590,10]])
                  drawRaw (scale $ transform s) (transform s) (readRawTex txp w h) (writeRawTex txp w h) w h font p
                  unlockTexture $ fst $ texture s
                  renderCopyFull rend (fst $ texture s)
                  renderPresent rend
              else pure ()
              ev0 <- waitEvent
              evs <- pollEvents ev0
              if elem AppQuit evs then pure () else do
                  (d,s') <- foldlM (updateState window rend) (False,s) evs
                  loop window rend font d s'

export
renderPictureGraph : PictureGraph 0 -> IO ()
renderPictureGraph = renderPicture . fst . processGraph . preProcessGraph . applyReroutes . convertGraph
