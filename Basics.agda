module Basics where

postulate
  Level  : Set
  lze    : Level
  lsu    : Level -> Level
  lmax   : Level -> Level -> Level

{-# BUILTIN LEVEL         Level  #-}
{-# BUILTIN LEVELZERO     lze    #-}
{-# BUILTIN LEVELSUC      lsu    #-}
{-# BUILTIN LEVELMAX      lmax   #-}

id : forall {i}{X : Set i} -> X -> X
id x = x

_o_ :  forall {i j k}
       {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
       (f : {a : A}(b : B a) -> C a b)
       (g : (a : A) -> B a)
       (a : A) -> C a (g a)
(f o g) a = f (g a)

data Zero : Set where

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

record One : Set where constructor <>

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 4 _*_ _,_

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}
infix 1 _==_

cong : forall {k l}{S : Set k}{T : Set l}(f : S -> T){s s' : S} ->
       s == s' -> f s == f s'
cong f refl = refl

_=!!_>>_ : forall {l}{X : Set l}(x : X){y z} -> x == y -> y == z -> x == z
_ =!! refl >> q = q

_<<_!!=_ : forall {l}{X : Set l}(x : X){y z} -> y == x -> y == z -> x == z
_ << refl !!= q = q

_<QED> : forall {l}{X : Set l}(x : X) -> x == x
x <QED> = refl

infixr 1 _=!!_>>_ _<<_!!=_ _<QED>

trans : forall {l}{X : Set l}{x y z : X} -> x == y -> y == z -> x == z
trans refl q = q

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO ze #-}
{-# BUILTIN SUC su #-}

data Vec (X : Set) : Nat -> Set where
  [] : Vec X ze
  _,_ : forall {n} -> X -> Vec X n -> Vec X (su n)
