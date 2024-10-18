module VerifiedOrd

import Data.So

%default total

public export
reverse : Ordering -> Ordering
reverse LT = GT
reverse EQ = EQ
reverse GT = LT

reverseReverse : (a:Ordering) -> reverse (reverse a) = a
reverseReverse LT = Refl
reverseReverse EQ = Refl
reverseReverse GT = Refl

reverseInjective : (a:Ordering) -> (b:Ordering) -> reverse a = reverse b -> a = b
reverseInjective a b eq = trans (rewrite__impl (\x => a = reverse x) (sym eq) $ sym $ reverseReverse a) (reverseReverse b)

-- This very awkwardly overlaps with VerifiedOrd, but having VerifiedOrd inherit from this doesn't work right.
public export
interface (Eq a) => VerifiedEq a where
    reflexiveE : (x:a) -> So (x == x)
    eqTransitiveE : (x:a) -> (y:a) -> (z:a) -> So (x == y) -> So (y == z) -> So (x == z)
    neqConsistentE : (x:a) -> (y:a) -> (x /= y) = not (x == y)
    exactE : (x:a) -> (y:a) -> So (x == y) -> x = y

public export
interface (Ord a, Eq a) => VerifiedOrd a where
    reflexive : (x:a) -> So (x == x)
    eqTransitive : (x:a) -> (y:a) -> (z:a) -> So (x == y) -> So (y == z) -> So (x == z)
    neqConsistent : (x:a) -> (y:a) -> (x /= y) = not (x == y)
    exact : (x:a) -> (y:a) -> So (x == y) -> x = y
    
    ltConsistent : (x:a) -> (y:a) -> (x < y) = (compare x y == LT)
    gtConsistent : (x:a) -> (y:a) -> (x > y) = (compare x y == GT)
    lteConsistent : (x:a) -> (y:a) -> (x <= y) = (compare x y /= GT)
    gteConsistent : (x:a) -> (y:a) -> (x >= y) = (compare x y /= LT)
    eqConsistent : (x:a) -> (y:a) -> (x == y) = (compare x y == EQ)
    reversable : (x:a) -> (y:a) -> compare x y = reverse (compare y x)
    ltTransitive : (x:a) -> (y:a) -> (z:a) -> So (x < y) -> So (y < z) -> So (x < z)

VerifiedEq Ordering where
    reflexiveE LT = Oh
    reflexiveE EQ = Oh
    reflexiveE GT = Oh
    eqTransitiveE LT LT LT Oh Oh = Oh
    eqTransitiveE EQ EQ EQ Oh Oh = Oh
    eqTransitiveE GT GT GT Oh Oh = Oh
    neqConsistentE x y = Refl
    exactE LT LT Oh = Refl
    exactE EQ EQ Oh = Refl
    exactE GT GT Oh = Refl

export
ltGtConsistent : VerifiedOrd a => (x:a) -> (y:a) -> (x < y) = (y > x)
ltGtConsistent x y = trans (ltConsistent x y) $ trans flipCompares (sym $ gtConsistent y x)
    where rv : compare x y == LT = reverse (compare x y) == GT
          rv with (compare x y)
              rv | LT = Refl
              rv | EQ = Refl
              rv | GT = Refl
          flipCompares : compare x y == LT = compare y x == GT
          flipCompares = rewrite__impl (\r => compare x y == LT = r == GT) (reversable y x) rv

export
ltGteConsistent : VerifiedOrd a => (x:a) -> (y:a) -> not (x < y) = (x >= y)
ltGteConsistent x y = rewrite__impl (\nc => not nc = x >= y) (ltConsistent x y) $ sym (gteConsistent x y)

export
gtLteConsistent : VerifiedOrd a => (x:a) -> (y:a) -> not (x > y) = (x <= y)
gtLteConsistent x y = rewrite__impl (\nc => not nc = x <= y) (gtConsistent x y) $ sym (lteConsistent x y)

export
ltLteConsistent : VerifiedOrd a => (x:a) -> (y:a) -> not (x < y) = (y <= x)
ltLteConsistent x y = rewrite__impl (\c => not c = (y <= x)) (ltGtConsistent x y) (gtLteConsistent y x)

export
gtGteConsistent : VerifiedOrd a => (x:a) -> (y:a) -> not (x > y) = (y >= x)
gtGteConsistent x y = rewrite__impl (\c => not c = (y >= x)) (sym $ ltGtConsistent y x) (ltGteConsistent y x)

export
lteCases : VerifiedOrd a => (x:a) -> (y:a) -> So (x <= y) -> Either (So (x < y)) (x = y)
lteCases x y lte with (compare x y) proof p
    lteCases x y lte | LT = Left $ replace (sym $ ltConsistent x y) $ rewrite__impl (\c => So $ compare x y == c) p $ reflexiveE (compare x y)
    lteCases x y lte | EQ = Right $ exact x y $ replace (sym $ eqConsistent x y) $ rewrite__impl (\c => So $ compare x y == c) p $ reflexiveE (compare x y)
    lteCases x y lte | GT = absurd $ the (So False) $ rewrite__impl (\c => So (c /= GT)) p $ replace (lteConsistent x y) lte

export
gteCases : VerifiedOrd a => (x:a) -> (y:a) -> So (x >= y) -> Either (So (x > y)) (x = y)
gteCases x y gte with (compare x y) proof p
    gteCases x y gte | LT = absurd $ the (So False) $ rewrite__impl (\c => So (c /= LT)) p $ replace (gteConsistent x y) gte
    gteCases x y gte | EQ = Right $ exact x y $ replace (sym $ eqConsistent x y) $ rewrite__impl (\c => So $ compare x y == c) p $ reflexiveE (compare x y)
    gteCases x y gte | GT = Left $ replace (sym $ gtConsistent x y) $ rewrite__impl (\c => So $ compare x y == c) p $ reflexiveE (compare x y)

export
ltImpliesLte : VerifiedOrd a => (x:a) -> (y:a) -> So (x < y) -> So (x <= y)
ltImpliesLte x y xy with (x <= y) proof p
    ltImpliesLte x y xy | True = Oh
    ltImpliesLte x y xy | False = void $ trueNotFalse $ replace (sym p) $ sym $ rewrite__impl (\c => x <= y = c /= GT) (sym $ exactE (compare x y) LT $ replace (ltConsistent x y) xy) (lteConsistent x y)

export
eqImpliesLte : VerifiedOrd a => (x:a) -> (y:a) -> So (x == y) -> So (x <= y)
eqImpliesLte x y xy with (x <= y) proof p
    eqImpliesLte x y xy | True = Oh
    eqImpliesLte x y xy | False = void $ trueNotFalse $ replace (sym p) $ sym $ rewrite__impl (\c => x <= y = c /= GT) (sym $ exactE (compare x y) EQ $ replace (eqConsistent x y) xy) (lteConsistent x y)

export
gtImpliesGte : VerifiedOrd a => (x:a) -> (y:a) -> So (x > y) -> So (x >= y)
gtImpliesGte x y xy with (x >= y) proof p
    gtImpliesGte x y xy | True = Oh
    gtImpliesGte x y xy | False = void $ trueNotFalse $ replace (sym p) $ sym $ rewrite__impl (\c => x >= y = c /= LT) (sym $ exactE (compare x y) GT $ replace (gtConsistent x y) xy) (gteConsistent x y)

export
eqImpliesGte : VerifiedOrd a => (x:a) -> (y:a) -> So (x == y) -> So (x >= y)
eqImpliesGte x y xy with (x >= y) proof p
    eqImpliesGte x y xy | True = Oh
    eqImpliesGte x y xy | False = void $ trueNotFalse $ replace (sym p) $ sym $ rewrite__impl (\c => x >= y = c /= LT) (sym $ exactE (compare x y) EQ $ replace (eqConsistent x y) xy) (gteConsistent x y)

export
gtTransitive : VerifiedOrd a => (x:a) -> (y:a) -> (z:a) -> So (x > y) -> So (y > z) -> So (x > z)
gtTransitive x y z xy yz = replace (ltGtConsistent z x) $ ltTransitive z y x (replace (sym $ ltGtConsistent z y) yz) (replace (sym $ ltGtConsistent y x) xy)

export
lteTransitive : VerifiedOrd a => (x:a) -> (y:a) -> (z:a) -> So (x <= y) -> So (y <= z) -> So (x <= z)
lteTransitive x y z xy yz with (lteCases x y xy)
    lteTransitive x y z xy yz | (Right xy') = rewrite__impl (\x' => So $ x' <= z) xy' yz
    lteTransitive x y z xy yz | (Left xy') with (lteCases y z yz)
        lteTransitive x y z xy yz | (Left xy') | (Right yz') = rewrite__impl (\y' => So $ x <= y') (sym yz') xy
        lteTransitive x y z xy yz | (Left xy') | (Left yz') = ltImpliesLte x z $ ltTransitive x y z xy' yz'

export
gtGteTransitive : VerifiedOrd a => (x:a) -> (y:a) -> (z:a) -> So (x > y) -> So (y >= z) -> So (x > z)
gtGteTransitive x y z xy yz with (gteCases y z yz)
    gtGteTransitive x y z xy yz | (Right yz') = rewrite__impl (\y' => So $ x > y') (sym yz') xy
    gtGteTransitive x y z xy yz | (Left yz') = gtTransitive x y z xy yz'

export
gteTransitive : VerifiedOrd a => (x:a) -> (y:a) -> (z:a) -> So (x >= y) -> So (y >= z) -> So (x >= z)
gteTransitive x y z xy yz with (gteCases x y xy)
    gteTransitive x y z xy yz | (Right xy') = rewrite__impl (\x' => So $ x' >= z) xy' yz
    gteTransitive x y z xy yz | (Left xy') = gtImpliesGte x z $ gtGteTransitive x y z xy' yz

export
ltIrreflexive : VerifiedOrd a => (x:a) -> So (x < x) -> Void
ltIrreflexive x xlx = absurd $ the (So $ EQ == LT) $ rewrite__impl (\c => So $ c == LT) (sym $ exactE (compare x x) EQ $ rewrite__impl So (sym $ eqConsistent x x) (reflexive x)) $ replace (ltConsistent x x) xlx

export
gtIrreflexive : VerifiedOrd a => (x:a) -> So (x > x) -> Void
gtIrreflexive x xgx = absurd $ the (So $ EQ == GT) $ rewrite__impl (\c => So $ c == GT) (sym $ exactE (compare x x) EQ $ rewrite__impl So (sym $ eqConsistent x x) (reflexive x)) $ replace (gtConsistent x x) xgx
