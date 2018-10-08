module Poker.Deck

import Control.ST
import Control.ST.Random
import Data.Fin
import Data.Vect

%access public export
%default total

elemSmallerThanBound : (n : Fin m) -> LT (finToNat n) m
elemSmallerThanBound FZ = LTESucc LTEZero
elemSmallerThanBound (FS x) = LTESucc (elemSmallerThanBound x)

data Suit = Spade | Heart | Diamond | Club

DecEq Suit where
  decEq Spade Spade = Yes Refl
  decEq Spade Heart = No $ \Refl impossible
  decEq Spade Diamond = No $ \Refl impossible
  decEq Spade Club = No $ \Refl impossible
  decEq Heart Spade = No $ \Refl impossible
  decEq Heart Heart = Yes Refl
  decEq Heart Diamond = No $ \Refl impossible
  decEq Heart Club = No $ \Refl impossible
  decEq Diamond Spade = No $ \Refl impossible
  decEq Diamond Heart = No $ \Refl impossible
  decEq Diamond Diamond = Yes Refl
  decEq Diamond Club = No $ \Refl impossible
  decEq Club Spade = No $ \Refl impossible
  decEq Club Heart = No $ \Refl impossible
  decEq Club Diamond = No $ \Refl impossible
  decEq Club Club = Yes Refl

Rank : Type
Rank = Fin 13

record Card where
  constructor MkCard
  suit : Suit
  rank : Rank

enumFinHelp : (b : Nat) -> Vect a (Fin a) -> Vect (b + a) (Fin (b + a))
enumFinHelp Z xs = xs
enumFinHelp {a} (S k) xs =
  let  xs' = last :: map weaken xs
  in rewrite plusSuccRightSucc k a in
  enumFinHelp k xs'

enumFin : (n : Nat) -> Vect n (Fin n)
enumFin n =
  rewrite sym (plusZeroRightNeutral n) in
  enumFinHelp n []

outerBy : (a -> b -> c) -> Vect m a -> Vect n b -> Vect (m * n) c
outerBy {m} {n} f xs ys =
  concat {m = m} {n = n} $ map (\x => map (f x) ys) xs

suits : Vect 4 Suit
suits = [Spade, Heart, Diamond, Club]

ranks : Vect 13 Rank
ranks = enumFin 13

ace : Rank
ace = the Rank last

newDeck : Vect 52 Card
newDeck =
  let ss = suits
      rs = ranks
  in outerBy MkCard ss rs

data Cut : (m : Nat) -> Vect o t -> Type where
  MkCut : (f : Vect m t) ->
          (c : t) ->
          (b : Vect n t) ->
          Cut m (f ++ c :: b)

plusOnePlusSucc : (m : Nat) -> (i' : Nat) -> plus (plus m 1) i' = S (plus m i')
plusOnePlusSucc m i' = rewrite plusCommutative m 1 in Refl

cutHelp : (f : Vect m t ) ->
          (b : Vect (S n) t ) ->
          (i : Nat) ->
          (lt : LT i (S n)) ->
          Cut (m + i) (f ++ b)
cutHelp {m = m} {n = n} f (c :: b) Z lt =
  rewrite plusZeroRightNeutral m in
  MkCut f c b
cutHelp {m = m} {n = Z} f (c :: b) (S i') (LTESucc lt') = absurd lt'
cutHelp {m = m} {n = (S n')} f (c :: b) (S i') (LTESucc lt') =
  let rec = cutHelp (f ++ [c]) b i' lt'
  in rewrite vectAppendAssociative f [c] b in
     rewrite sym $ plusSuccRightSucc m i' in
     rewrite sym $ plusOnePlusSucc m i' in
     rec

cut : (i : Nat) -> (xs : Vect n t) ->
      {auto smaller : LT i n} ->
      Cut i xs
cut {n = Z} i xs {smaller = smaller} = absurd smaller
cut {n = (S k)} i xs {smaller = smaller} = cutHelp [] xs i smaller

data Shuffle : Vect n t -> Type where
  EmptyShuffle : (xs : Vect Z t) -> Shuffle xs
  Deal : (c : t) -> Shuffle (f ++ b) -> Shuffle (f ++ c :: b)

mutual
  shuffleHelp : (rnd : Var) -> (xs : Vect n t) ->
                (i : Fin n) ->
                ST m (Shuffle xs) [rnd ::: Random]
  shuffleHelp {t} rnd xs i with (elemSmallerThanBound i)
    shuffleHelp {t} rnd xs i | lt with (finToNat i)
      shuffleHelp {t} rnd xs i | lt | i' with (cut i' xs)
        shuffleHelp {t} rnd (f ++ c :: b) i | lt | i' | (MkCut f c b) = do
          rest <- shuffle rnd $ assert_smaller (f ++ c :: b) (f ++ b)
          pure (Deal {t = t} {f = f} {b = b} c rest)

  shuffle : (rnd : Var) -> (xs : Vect n t) -> ST m (Shuffle xs) [rnd ::: Random]
  shuffle {n = Z} rnd [] = pure (EmptyShuffle [])
  shuffle {n = (S n')} rnd xs = do
    i <- rndFin rnd n'
    shuffleHelp rnd xs i

-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
