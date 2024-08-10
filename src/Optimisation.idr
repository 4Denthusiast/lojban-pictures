module Optimisation

import Data.Fin
import Data.SortedMap
import Data.Vect

-- A non-linear unconstrained optimisation problem in n variables, where p represents in some way an n-dimensional vector
record OptLandscape (pt:Type) (n:Nat)
    getCoordinate : Fin n -> pt -> Double
    setCoordinate : Fin n -> Double -> pt -> pt
    setCoordinates : Vect n Double -> pt
    getEnergy : pt -> Double
    getDerivative : Fin n -> pt -> Double

-- line search in the direction of one coordinate axis, using Wolfe conditions
cardinalLineSearch : OptLandscape pt n -> pt -> Fin n -> pt
cardinalLineSearch l p i = let
        e0 = getEnergy l p
        de0 = getDerivative l i p
        x0 = getCoordinate l i p
        p' x = setCoordinate l i (x0 - x * sgn de0) p
        e' x = getEnergy l (p' x) - e0
        d' x = - sgn de0 * getDerivative l i (p' x)
        tooFar x = e' x > de0 * x * 0.1
        tooNear x = d' x < -0.9 * abs de0
        search xn xf = let x = (xn+fx)/2 in
            if (tooFar x) then search xn x
            else if (tooNear x) then search x xf
            else x
        searchNear = search 0
        searchFar xn = let x = xn*2 in
            if (tooFar x) then search xn x
            else if (tooNear x) then searchFar x
            else x
        searchAll =
            if (tooFar 1) then searchNear 1
            else if (tooNear 1) then searchFar 1
            else 1
    in setCoordinate l i (x0 + sgn de0 * searchAll) p

-- Search along the single coordinate of steepest descent
export
cardinalGradientDescent : OptLandscape pt n -> pt -> Stream pt
cardinalGradientDescent l p = iterate descendStep p
    where descendStep p' = cardinalLineSearch l p' (steepestDirection p')
          steepestDirection p' = Basics.snd $ minimum $ map (\i => (abs $ getDerivative l i p', i)) range

-- Select the iterate where the rate of convergence has been less than t on average for about the last n values.
export
energyConvergence : OptLandscape pt n -> Double -> Double -> Stream pt -> pt
energyConvergence l n t (p::ps) = c' (getEnergy l p + t*n*2) ps
    where c' e (p::ps) = let ep = getEnergy l p in if e - ep < t then p else c' (e + (ep-e)/n) ps
