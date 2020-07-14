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

sum_tail_correct' : (n : Nat) -> (l : List Nat) -> sum_tail' l n = n + sum' l
sum_tail_correct' n [] = rewrite plusZeroRightNeutral n in Refl
sum_tail_correct' n (x :: xs) =
    rewrite plusCommutative x n in
    rewrite plusAssociative n x (sum' xs) in sum_tail_correct' (n + x) xs

sum_tail_correct : sum_tail l = sum' l
sum_tail_correct {l} = sum_tail_correct' 0 l

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

------------Reverse-------------------------------------

rev : (l : List a) -> List a
rev [] = []
rev (x :: xs) = rev xs ++ [x]

rev_tail' : (l : List a) -> (acc : List a) -> List a
rev_tail' [] acc = acc
rev_tail' (x :: xs) acc = rev_tail' xs (x :: acc)

rev_tail_correct' : (l : List a) -> (acc : List a) -> rev_tail' l acc = rev l ++ acc
rev_tail_correct' [] acc = Refl
rev_tail_correct' (x :: xs) acc =
  rewrite rev_tail_correct' xs (x :: acc) in
  rewrite appendAssociative (rev xs) [x] acc in Refl

rev_tail : (l : List a) -> List a
rev_tail l = rev_tail' l []

rev_tail_correct : (l : List l) -> rev_tail l = rev l
rev_tail_correct l =
  rewrite sym(appendNilRightNeutral (rev l)) in
  rewrite rev_tail_correct' l [] in Refl

--------------Map-----------------------------------

map' : (f : a -> b) -> (l : List a) -> List b
map' f [] = []
map' f (x :: xs) = f x :: map' f xs

map_tail' : (f : a -> b) -> (l : List a) -> (acc : List b) -> List b
map_tail' f [] acc = rev_tail acc
map_tail' f (x :: xs) acc = map_tail' f xs (f x :: acc)

map_tail : (f : a -> b) -> (l : List a) -> List b
map_tail f l = map_tail' f l []

map_tail_correct' :
  (f : a -> b) ->
  (l : List a) ->
  (acc : List b) ->
  map_tail' f l acc = rev_tail acc ++ map' f l
map_tail_correct' f [] acc = rewrite appendNilRightNeutral (rev_tail' acc []) in Refl
map_tail_correct' f (x :: xs) acc =
  rewrite map_tail_correct' f xs (f x :: acc) in
  rewrite rev_tail_correct (f x :: acc) in
  rewrite rev_tail_correct acc in
  rewrite appendAssociative (rev acc) [f x] (map' f xs) in Refl

map_tail_correct : map_tail f l = map' f l
map_tail_correct {f} {l} = map_tail_correct' f l []
