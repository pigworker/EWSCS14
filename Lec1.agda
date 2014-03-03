module Lec1 where

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

_+_ : Nat -> Nat -> Nat
ze + y = y
su x + y = su (x + y)

data Vec (X : Set) : Nat -> Set where
  [] : Vec X ze
  _,_ : forall {n} -> X -> Vec X n -> Vec X (su n)
infixr 4 _,_

zapp : forall {S T n} -> Vec (S -> T) n -> Vec S n -> Vec T n
zapp [] [] = []
zapp (f , fs) (s , ss) = f s , zapp fs ss

_++_ : forall {m n X} -> Vec X m -> Vec X n -> Vec X (m + n)
[] ++ ys = ys
(x , xs) ++ ys = x , xs ++ ys

vec : forall {n X} -> X -> Vec X n
vec {ze} x = []
vec {su n} x = x , vec x

myVec : Vec Nat (su (su (su (su (su ze)))))
myVec = vec (su ze)
