module UPolyBasics where


postulate
      Level : Set
      lze  : Level
      lsu   : Level -> Level
      lmax   : Level -> Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lze   #-}
{-# BUILTIN LEVELSUC  lsu   #-}
{-# BUILTIN LEVELMAX  lmax  #-}

_o_ : forall {i j k}
        {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k} ->
        (f : {a : A}(b : B a) -> C a b) ->
        (g : (a : A) -> B a) ->
        (a : A) -> C a (g a)
f o g = \ a -> f (g a)

id : forall {k}{X : Set k} -> X -> X
id x = x

record Sg {l : Level}(S : Set l)(T : S -> Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
_*_ : {l : Level} -> Set l -> Set l -> Set l
S * T = Sg S \ _ -> T
infixr 4 _,_ _*_

vv_ :  forall {k l}{S : Set k}{T : S -> Set k}{P : Sg S T -> Set l} ->
      ((s : S)(t : T s) -> P (s , t)) ->
      (p : Sg S T) -> P p
(vv p) (s , t) = p s t
infixr 1 vv_

record One {l : Level} : Set l where
  constructor <>
open One public

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
infix 1 _==_
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

subst :  forall {k l}{X : Set k}{s t : X} ->
         s == t -> (P : X -> Set l) -> P s -> P t
subst refl P p = p


_=!!_>>_ : forall {l}{X : Set l}(x : X){y z} -> x == y -> y == z -> x == z
_ =!! refl >> q = q

_<<_!!=_ : forall {l}{X : Set l}(x : X){y z} -> y == x -> y == z -> x == z
_ << refl !!= q = q

_<QED> : forall {l}{X : Set l}(x : X) -> x == x
x <QED> = refl

infixr 1 _=!!_>>_ _<<_!!=_ _<QED>

cong : forall {k l}{X : Set k}{Y : Set l}(f : X -> Y){x y} -> x == y -> f x == f y
cong f refl = refl

data Zero {l} : Set l where

magic : forall {k l}{A : Set l} -> Zero {k} -> A
magic ()

data _+_ {l}(S T : Set l) : Set l where
  inl : S -> S + T
  inr : T -> S + T

Dec : forall {l} -> Set l -> Set l
Dec {l} X = X + (X -> Zero {l})

data List {l}(X : Set l) : Set l where
  <> : List X
  _,_ : X -> List X -> List X


data Nat : Set where
  ze : Nat
  su : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO ze #-}
{-# BUILTIN SUC su #-}

record Cum {l}(X : Set l) : Set (lsu l) where
  constructor up
  field
    down : X
