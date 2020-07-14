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

----------Expression languages-----------------------------

data Expr : Type where
  Const : Nat -> Expr
  Plus : Expr -> Expr -> Expr

eval_expr : (e : Expr) -> Nat
eval_expr (Const n) = n
eval_expr (Plus e1 e2) = eval_expr e1 + eval_expr e2

eval_expr_tail' : (e : Expr) -> (acc : Nat) -> Nat
eval_expr_tail' (Const n) acc = n + acc
eval_expr_tail' (Plus e1 e2) acc = eval_expr_tail' e2 (eval_expr_tail' e1 acc)

eval_expr_tail_correct' :
  (e : Expr) ->
  (acc : Nat) ->
  eval_expr_tail' e acc = eval_expr e + acc
eval_expr_tail_correct' (Const k) acc = Refl
eval_expr_tail_correct' (Plus x y) acc =
  rewrite eval_expr_tail_correct' y (eval_expr_tail' x acc) in
  rewrite eval_expr_tail_correct' x acc in
  rewrite plusAssociative (eval_expr y) (eval_expr x) acc in
  rewrite plusCommutative (eval_expr y) (eval_expr x) in Refl

eval_expr_tail : (e : Expr) -> Nat
eval_expr_tail e = eval_expr_tail' e 0

eval_expr_tail_correct : eval_expr_tail e = eval_expr e
eval_expr_tail_correct {e} =
  rewrite sym(plusZeroRightNeutral (eval_expr e)) in eval_expr_tail_correct' e 0

--------------------Continuation-passing style evaluator-------------------------

eval_expr_cont' : (e : Expr) -> (k : Nat -> a) -> a
eval_expr_cont' (Const n) k = k n
eval_expr_cont' (Plus e1 e2) k =
  eval_expr_cont' e2 (\n2 => eval_expr_cont' e1 (\n1 => k (n1 + n2)))

eval_expr_cont : (e : Expr) -> Nat
eval_expr_cont e = eval_expr_cont' e (\n => n)

eval_expr_cont_correct' :
  (e : Expr) ->
  (k : Nat -> a) ->
  eval_expr_cont' e k = k (eval_expr e)
eval_expr_cont_correct' (Const j) k = Refl
eval_expr_cont_correct' (Plus x y) k =
  rewrite eval_expr_cont_correct' y (\n2 => eval_expr_cont' x (\n1 => k (plus n1 n2))) in
  rewrite eval_expr_cont_correct' x (\n1 => k (plus n1 (eval_expr y))) in Refl

eval_expr_cont_correct : eval_expr_cont e = eval_expr e
eval_expr_cont_correct {e} = eval_expr_cont_correct' e (\n => n)
