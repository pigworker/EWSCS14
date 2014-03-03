module Lec2 where

open import Basics

Two : Set
Two = One + One

Le : Nat -> Nat -> Set
Le ze y = One
Le (su x) ze = Zero
Le (su x) (su y) = Le x y

record Prf (P : Set) : Set where
  constructor !
  field
    {{.prf}} : P

pattern lte = inl !
pattern gte = inr !

le : forall x y -> Prf (Le x y) + Prf (Le y x)
le ze y = lte
le (su x) ze = gte
le (su x) (su y) = le x y

data Bound : Set where
  bot : Bound
  [_] : Nat -> Bound
  top : Bound

LeB : Bound -> Bound -> Set
LeB bot _ = One
LeB _ bot = Zero
LeB _ top = One
LeB top _ = Zero
LeB [ x ] [ y ] = Le x y

data BST (l u : Bound) : Set where
  leafp : Prf (LeB l u) -> BST l u
  pnode : (p : Nat) -> BST l [ p ] -> BST [ p ] u -> BST l u
pattern leaf = leafp !
pattern node l p r = pnode p l r

IntV : Bound -> Bound -> Set
IntV l u = Sg Nat \ p -> Prf (LeB l [ p ]) * Prf (LeB [ p ] u)
pattern iv x = x , ! , !

insert : forall {l u} -> IntV l u -> BST l u -> BST l u
insert (iv x) leaf = node leaf x leaf
insert (iv x) (node l y r) with le x y
insert (iv x) (node l y r) | lte = node (insert (iv x) l) y r
insert (iv x) (node l y r) | gte = node l y (insert (iv x) r)

{- with le x y
insert (x , ! , !) (pnode y l r) | lte
  = node (insert (x , ! , !) l) y r
insert (x , ! , !) (pnode y l r) | gte
  = node l y (insert (x , ! , !) r)
-}

