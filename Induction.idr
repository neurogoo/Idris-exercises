module Induction

%default total

sum' : List Nat -> Nat
sum' [] = 0
sum' (x :: xs) = x + sum' xs

------------Tail-recursive sum-----------------------

sum_tail' : List Nat -> Nat -> Nat
sum_tail' [] acc = acc
sum_tail' (x :: xs) acc = sum_tail' xs (x + acc)

sum_tail : List Nat -> Nat
sum_tail l = sum_tail' l 0

canTakeBaseValueOut : (n : Nat) -> (l : List Nat) -> n + sum_tail' l 0 = sum_tail' l n
canTakeBaseValueOut n [] = rewrite plusZeroRightNeutral n in Refl
canTakeBaseValueOut n (x :: xs) =
  rewrite plusZeroRightNeutral x in
  rewrite sym(canTakeBaseValueOut x xs) in
  rewrite sym(canTakeBaseValueOut (x + n) xs) in
  rewrite plusAssociative n x (sum_tail' xs 0) in
  rewrite plusCommutative n x in Refl

addingToSumSameAsAddingToList : sum_tail' (x :: xs) 0 = x + sum_tail' xs 0
addingToSumSameAsAddingToList {x} {xs = []} = Refl
addingToSumSameAsAddingToList {x} {xs = (y :: ys)} =
  rewrite plusZeroRightNeutral x in
  rewrite plusZeroRightNeutral y in
  rewrite plusCommutative y x in
  rewrite sym(canTakeBaseValueOut y ys) in
  rewrite sym(canTakeBaseValueOut (x + y) ys) in
  rewrite plusAssociative x y (sum_tail' ys 0) in Refl

sum_tail_correct : sum_tail l = sum' l
sum_tail_correct {l = []} = Refl
sum_tail_correct {l = (x :: xs)} =
  rewrite addingToSumSameAsAddingToList {x} {xs} in cong(sum_tail_correct)

------------Continuation-passing style sum-----------------------

sum_cont' : (l : List Nat) -> (k : Nat -> a) -> a
sum_cont' [] k = k 0
sum_cont' (x :: xs) k = sum_cont' xs (\ans => k (x + ans))

sum_cont : (l : List Nat) -> Nat
sum_cont l = sum_cont' l (\x => x)

sum_cont_correct' :
  (k : Nat -> a) ->
  (l : List Nat) -> sum_cont' l k = k(sum' l)
sum_cont_correct' k [] = Refl
sum_cont_correct' k (x :: xs) = sum_cont_correct' (\acc => k (plus x acc)) xs

sum_cont_correct : sum_cont l = sum' l
sum_cont_correct {l} = sum_cont_correct' (\x => x) l
