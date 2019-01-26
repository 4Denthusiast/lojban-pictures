module Render

import Picture
import Words
import Graph
import GraphSubstitution

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
    guard (any (\((s,_),_) => case s of {Reroute _ => True; RerouteAny => True; _ => False}) es)
    let (es1,rrs) = the (List (PictureEdgeLabel,NodeLabel), List (PictureStubLabel, (PictureStubLabel, NodeLabel))) $ partitionEithers $ (\((ns,fs),nl') => case ns of {Reroute s => Right (s,fs,nl'); _ => Left ((ns,fs),nl')}) <$> es
    let rrs' = the (SortedMap PictureStubLabel (PictureStubLabel, NodeLabel)) $ fromList rrs
    let (es2,newEdges0) = the (List (PictureEdgeLabel,NodeLabel),List (Edge PictureEdgeLabel)) $ partitionEithers $ (\((ns,fs),nl') => case (SortedMap.lookup ns rrs') of
            Just (fs',nl'') => Right (MkEdge nl' nl'' (fs,fs'))
            Nothing => Left ((ns,fs),nl')
        ) <$> es1
    let anyBackNodes = map Basics.snd $ filter (\((_,fs),_) => fs == RerouteAny) es2
    anyBackNodes' <- for anyBackNodes (\nl' =>
            (\ss => (nl',ss)) <$>
            the (SortedSet PictureStubLabel) <$> fromList <$>
            catMaybes <$>
            map (\s => case s of {Reroute s' => Just s'; _ => Nothing}) <$>
            map (\(_,(s,_),_) => s) <$>
            getAdjEdges' g nl'
        )
    let newEdges1 = the (List (Edge PictureEdgeLabel)) $ catMaybes $ (\(s,fs,nl), (nl',ss) => if contains s ss then Nothing else Just (MkEdge nl' nl (Reroute s,fs))) <$> rrs <*> anyBackNodes'
    let (es3, anyForwardNodes) = the (List (PictureEdgeLabel,NodeLabel),List NodeLabel) $ map (map Basics.snd) $ partition (\((s,_),_) => s /= RerouteAny) es2
    let newEdges2 = case anyForwardNodes of
        [] => []
        (nl'::_) => map (\((ns,fs),nl'') => MkEdge nl' nl'' (ns,fs)) es3
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
    pics <- for es' (\(MkEdge nl0' nl1' (s0,s1),nl1) => do
            (lPic, lStubs) <- getNode g nl1
            bs <- lookup (nl0', s0) bStubs
            ls <- lookup (nl1', s1) lStubs
            pure $ Transformed (MkTransform bs 1) $ Line [0,0] [0,2] <+> Transformed (MkTransform (MkPosition [0,2] back <-> ls) 1) lPic
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

Eq DisplayState where
    (==) (MkState t p) (MkState t' p') = t == t' && p == p'

-- A transform so that the picture fits within the unit circle (with a margin)
normalisePlacementTransform : Picture -> Transform
normalisePlacementTransform p = let (c, r) = circumcircle $ pictureHull p
    in scaleTransform (1/(r+1)) <+> translateTransform (inverse c)

renderPicture : Picture -> IO ()
renderPicture p = do
        (ctx, rend) <- startSDL "Pretty lojban" 600 600
        font <- ttfOpenFont "/usr/share/fonts/truetype/freefont/FreeSans.ttf" 15
        loop rend font True (MkState (MkTransform (MkPosition [300,300] neutral) 300 <+> normalisePlacementTransform p) [0,0])
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
renderPictureGraph = renderPicture . fst . processGraph . preProcessGraph . applyReroutes . convertGraph
