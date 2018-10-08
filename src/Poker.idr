module Poker

import Control.ST
import Control.ST.Random
import Data.Fin
-- import Data.Fin.Extra
import Data.Vect
import Data.Vect.Views

import Poker.Deck

%default total

Hand : Type
Hand = Vect 7 Card

sort : Ord t => Vect n t -> Vect n t
sort xs with (splitRec xs)
  sort [] | SplitRecNil = []
  sort [x] | SplitRecOne = [x]
  sort (ys ++ zs) | (SplitRecPair lrec rrec) =
    merge (sort ys | lrec) (sort zs | rrec)

data SuitCount : Suit -> Vect n Card -> Nat -> Type where
  SuitEmpty : (h : Vect Z Card) -> SuitCount s h Z
  SuitMatch : (rec : SuitCount s h n) -> SuitCount s ((MkCard s r) :: h) (S n)
  SuitMiss : (rec : SuitCount s h n) ->
             (contra: Not (s = s')) ->
             SuitCount s ((MkCard s' r) :: h) (S n)

suitCount : (s : Suit) -> (h : Vect m Card) -> (n ** SuitCount s h n)
suitCount s [] = (0 ** SuitEmpty [])
suitCount s ((MkCard s' r) :: xs) =
  let (_ ** rec) = suitCount s xs
  in case decEq s s' of
    Yes Refl => (_ ** SuitMatch rec)
    No contra => (_ ** SuitMiss rec contra)

data Run : (b : Nat) -> (xs : Vect m Nat) -> (n : Nat) -> Type where
  EmptyRun : (xs : Vect m Nat) -> Run b xs Z
  Step : Elem (n + b) xs -> (rec : Run b xs n) -> Run b xs (S n)

data RankCount : Rank -> Vect n Card -> Nat -> Type where
  RankEmpty : (h : Vect Z Card) -> RankCount s h Z
  RankMatch : (rec : RankCount r h n) -> RankCount r ((MkCard s r) :: h) (S n)
  RankMiss : (rec : RankCount r h n) ->
             (contra: Not (r = r')) ->
             RankCount r ((MkCard s r') :: h) (S n)

rankCount : (r : Rank) -> (h : Vect m Card) -> (n ** RankCount r h n)
rankCount r [] = (0 ** RankEmpty [])
rankCount r ((MkCard s r') :: xs) =
  let (_ ** rec) = rankCount r xs
  in case decEq r r' of
    Yes Refl => (_ ** RankMatch rec)
    No contra => (_ ** RankMiss rec contra)

data Ranks : Vect 5 Rank -> Type where
  MkRanks : (rs : Vect 5 Rank) -> Ranks rs

data StraightRun : Hand -> Type where
  HighStraight : Run b (map (finToNat . Poker.Deck.Card.rank) h) 5 ->
                 StraightRun h
  LowStright : Elem Poker.Deck.ace (map Poker.Deck.Card.rank h) ->
               Run 0 (map (finToNat . Poker.Deck.Card.rank) h) 4 ->
               StraightRun h

data FlushRun : Hand -> Type where
  MkFlush : SuitCount s h n -> LTE 5 n -> FlushRun h

data Score : Hand -> Type where
  HighCard : Ranks (take 5 . reverse . Poker.sort $ map (Poker.Deck.Card.rank) h) ->
             Score h
  Pair : RankCount r h 2 -> Score h
  TwoPair : RankCount r h 2 -> RankCount s h 2 -> Not (r = s) -> Score h
  Trip : RankCount r h 3 -> Score h
  Straight : StraightRun h -> Score h
  Flush : FlushRun h -> Score h
  FullHouse : RankCount r h 3 -> RankCount s h 2 -> Score h
  FullHouse' : RankCount r h 3 -> RankCount s h 3 -> Not (r = s) -> Score h
  Quad : RankCount r h 4 -> Score h
  StraightFlush : StraightRun h -> FlushRun h -> Score h

isFlushHelp : (h : Hand) -> (s : Suit) -> Maybe (FlushRun h)
isFlushHelp h s with (suitCount s h)
  isFlushHelp h s | (n ** ss) with (isLTE 5 n)
    isFlushHelp h s | (n ** ss) | (Yes lte) = Just (MkFlush ss lte)
    isFlushHelp h s | (n ** ss) | (No contra) = Nothing

isFlush : (h : Hand) -> Maybe (FlushRun h)
isFlush h = foldr (<+>) Nothing (map (isFlushHelp h) suits)

checkRun : (b : Nat) -> (xs : Vect m Nat) -> (n : Nat) -> Maybe (Run b xs n)
checkRun b xs Z = Just (EmptyRun xs)
checkRun b xs (S n) =
  case isElem (n + b) xs of
    (Yes prf) => Step prf <$> checkRun b xs n
    (No contra) => Nothing

isStraightHelp : (h : Hand) -> (b : Nat) -> Maybe (StraightRun h)
isStraightHelp h b =
  HighStraight <$> checkRun b (map (finToNat . rank) h) 5

isLowStraight : (h : Hand) -> Maybe (StraightRun h)
isLowStraight h with (isElem ace (map rank h))
  isLowStraight h | (Yes prf) =
    (LowStright prf <$> checkRun 0 (map (finToNat . rank) h) 4)
  isLowStraight h | (No contra) = Nothing

isStraight : (h : Hand) -> Maybe (StraightRun h)
isStraight h =
  foldr (<+>) Nothing (map (isStraightHelp h . finToNat) ranks) <+>
  isLowStraight h

countRanks : (h : Hand) -> Vect 13 (r ** n ** RankCount r h n)
countRanks h = map (\r => (r ** rankCount r h)) (reverse ranks)

findReps : (c : Nat) ->
           Vect o (r ** n ** RankCount r h n) ->
           List (r' ** RankCount r' h c)
findReps c [] = []
findReps c (x :: xs) with (x)
  findReps c (x :: xs) | (r'' ** n' ** rc) =
    case decEq c n' of
      (Yes Refl) => (r'' ** rc) :: findReps c xs
      (No contra) => findReps c xs

findQuad : Vect o (r ** n ** RankCount r h n) ->
           Maybe (Score h)
findQuad rs with (findReps 4 rs)
  findQuad rs | [] = Nothing
  findQuad rs | ((r' ** rc) :: _) = Just (Quad rc)

findTrip : Vect o (r ** n ** RankCount r h n) ->
           Maybe (Score h)
findTrip rs with (findReps 3 rs)
  findTrip rs | [] = Nothing
  findTrip rs | ((r' ** rc) :: _) = Just (Trip rc)

findPairs : Vect o (r ** n ** RankCount r h n) ->
            Maybe (Score h)
findPairs rs with (findReps 2 rs)
  findPairs rs | ((r1 ** rc1) :: (r2 ** rc2) :: xs) =
    case decEq r1 r2 of
      (Yes prf) =>
        -- this should never happen, but handle it
        assert_total $ findPairs rs | ((r1 ** rc1) :: xs)
      (No contra) => Just (TwoPair rc1 rc2 contra)
  findPairs rs | ((r' ** rc) :: []) = Just (Pair rc)
  findPairs rs | [] = Nothing

findFH : Vect o (r ** n ** RankCount r h n) ->
         Maybe (Score h)
findFH rs with (findReps 3 rs)
  findFH rs | [] = Nothing
  findFH rs | (x :: []) with (findReps 2 rs)
    findFH rs | (x :: []) | [] = Nothing
    findFH rs | ((r1 ** rc1) :: []) | ((r2 ** rc2) :: _) = Just (FullHouse rc1 rc2)
  findFH rs | ((r1 ** rc1) :: (r2 ** rc2) :: ys) with (decEq r1 r2)
    findFH rs | ((r1 ** rc1) :: (r2 ** rc2) :: ys) | (Yes prf) =
      -- this should never happen, but handle it
      assert_total $ findFH rs | ((r1 ** rc1) :: ys)
    findFH rs | ((r1 ** rc1) :: (r2 ** rc2) :: _) | (No contra) with (findReps 2 rs)
      findFH rs | ((r1 ** rc1) :: (r2 ** rc2) :: _) | (No contra) | [] =
        Just (FullHouse' rc1 rc2 contra)
      findFH rs | ((r1 ** rc1) :: (r2 ** rc2) :: _) | (No contra) | ((r3 ** rc3) :: _) =
        if (r2 > r3)
        then Just (FullHouse' rc1 rc2 contra)
        else Just (FullHouse rc1 rc3)

score : (h : Hand) -> Score h
score h =
  let f = isFlush h
      s = isStraight h
      rs = countRanks h
      m = (StraightFlush <$> s <*> f) <+>
          (findQuad rs) <+>
          (findFH rs) <+>
          (Flush <$> f) <+>
          (Straight <$> s) <+>
          (findTrip rs) <+>
          (findPairs rs)
      hc = HighCard $ MkRanks (take 5 . reverse . sort $ map rank h)
  in maybe hc id m

-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:
