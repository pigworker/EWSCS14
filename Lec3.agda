module Lec3 where

-- https://github.com/pigworker/EWSCS14

open import Basics

{- types in the spotlight -}

{- polynomials -}

data Poly : Set where
  `X `0 `1 : Poly
  _`+_ _`*_ : Poly -> Poly -> Poly
infixr 4 _`+_
infixr 5 _`*_

Fun : Poly -> Set -> Set
Fun `X X = X
Fun `0 X = Zero
Fun `1 X = One
Fun (F `+ G) X = Fun F X + Fun G X
Fun (F `* G) X = Fun F X * Fun G X

data Mu (F : Poly) : Set where
  <_> : Fun F (Mu F) -> Mu F

`Nat = `1 `+ `X

-- `ze : Mu `Nat
pattern `ze = < inl <> >

-- `su : Mu `Nat -> Mu `Nat
pattern `su n = < inr n >


_`+N_ : Mu `Nat -> Mu `Nat -> Mu `Nat
`ze `+N y = y
`su x `+N y = `su (x `+N y)

{- traversal structure -}

record Applicative (R : Set -> Set) : Set1 where
  constructor applicative
  field
    pure   : forall {X} -> X -> R X
    _$_  : forall {S T} -> R (S -> T) -> R S -> R T
  infixl 7 _$_

trav : forall {R}(ar : Applicative R) F
       {S T} -> (S -> R T) -> Fun F S -> R (Fun F T)
trav {R} ar F {S} {T} r fs = go F fs where
  open Applicative ar
  go : forall F -> Fun F S -> R (Fun F T)
  go `X s = r s
  go `0 ()
  go `1 <> = pure <>
  go (G `+ H) (inl gs) = pure inl $ go G gs
  go (G `+ H) (inr hs) = pure inr $ go H hs
  go (G `* H) (gs , hs) = pure _,_ $ go G gs $ go H hs

map : forall F {S T} -> (S -> T) -> Fun F S -> Fun F T
map F = trav (applicative id id) F

fold : forall F {X M : Set} -> M -> (M -> M -> M) -> (X -> M) -> Fun F X -> M
fold F neutral combine =
  trav (applicative (\ _ -> neutral) combine) F {T = Zero}
{--}

{- making holes in types -}

D : Poly -> Poly
D `X = `1
D `0 = `0
D `1 = `0
D (F `+ G) = D F `+ D G
D (F `* G) = D F `* G `+ F `* D G

plug : forall {X} F -> Fun (D F) X -> X -> Fun F X
plug `X <> x = x
plug `0 () x
plug `1 () x
plug (F `+ G) (inl dfx) x = inl (plug F dfx x)
plug (F `+ G) (inr dgx) x = inr (plug G dgx x)
plug (F `* G) (inl (dfx , gx)) x = plug F dfx x , gx
plug (F `* G) (inr (fx , dgx)) x = fx , plug G dgx x

gulp : forall {X} F -> Fun F X -> Fun F (Fun (D F `* `X) X)
gulp {X} F fx = {!!}
{--}

{- Dependent types in the spotlight -}

data Desc (I : Set) : Set1 where
  -- Conor, if you have time, transform the polynomials and go by hand
  -- but if you're in a hurry, cheat

