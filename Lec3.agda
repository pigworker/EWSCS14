module Lec3 where

open import Basics

{- types in the spotlight -}

{- polynomials -}

data Poly : Set where
  `X `0 `1 : Poly
  _`+_ _`*_ : Poly -> Poly -> Poly
infixr 4 _`+_
infixr 5 _`*_

Fun : Poly -> Set -> Set
Fun F X = {!!}

{-
data Mu (F : Poly) : Set where
  <_> : Fun F (Mu F) -> Mu F
-}

`Nat = `1 `+ `X

--number : Mu `Nat
--number = {!-l!}

{-
_`+N_ : Mu `Nat -> Mu `Nat -> Mu `Nat
x `+N y = ?
-}

{- traversal structure

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
  go F fs = {!!}

map : forall F {S T} -> (S -> T) -> Fun F S -> Fun F T
map F = {!!}

fold : forall F {X M : Set} -> M -> (M -> M -> M) -> (X -> M) -> Fun F X -> M
fold F neutral combine = {!!}
-}

{- making holes in types

Holey : Poly -> Poly
Holey F = {!!}

plug : forall {X} F -> Fun (Holey F) X -> X -> Fun F X
plug F hfx x = ?

gulp : forall {X} F -> Fun F X -> Fun F (Fun (Holey F `* `X) X)
gulp {X} F fx = {!!}
-}

{- Dependent types in the spotlight -}

data Desc (I : Set) : Set1 where
  -- Conor, if you have time, transform the polynomials and go by hand
  -- but if you're in a hurry, cheat

