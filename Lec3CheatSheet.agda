module Lec3CheatSheet where

open import Basics

data Poly : Set where
  `X `0 `1 : Poly
  _`+_ _`*_ : Poly -> Poly -> Poly
infixr 4 _`+_
infixr 5 _`*_

Fun : Poly -> Set -> Set
Fun `X X = X
Fun `0 X = Zero
Fun `1 X = One
Fun (S `+ T) X = Fun S X + Fun T X
Fun (S `* T) X = Fun S X * Fun T X

data Mu (F : Poly) : Set where
  <_> : Fun F (Mu F) -> Mu F

`Nat = `1 `+ `X

--number : Mu `Nat
--number = {!-l!}

pattern `ze = < inl <> >
pattern `su n = < inr n >

_`+N_ : Mu `Nat -> Mu `Nat -> Mu `Nat
`ze `+N y = y
`su x `+N y = `su (x `+N y)

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
  go (F `+ G) (inl fs)   = pure inl $ go F fs
  go (F `+ G) (inr gs)   = pure inr $ go G gs
  go (F `* G) (fs , gs)  = pure _,_ $ go F fs $ go G gs

map : forall F {S T} -> (S -> T) -> Fun F S -> Fun F T
map F = trav (applicative id id) F

fold : forall F {X M : Set} -> M -> (M -> M -> M) -> (X -> M) -> Fun F X -> M
fold F neutral combine = trav (applicative (\ _ -> neutral) combine) F {T = Zero}

D : Poly -> Poly
D `X = `1
D `0 = `0
D `1 = `0
D (F `+ G) = D F `+ D G
D (F `* G) = (D F `* G) `+ (F `* D G)

plug : forall {X} F -> Fun (D F) X -> X -> Fun F X
plug `X <> x = x
plug `0 () x
plug `1 () x
plug (F `+ G) (inl dfx) x = inl (plug F dfx x)
plug (F `+ G) (inr dgx) x = inr (plug G dgx x)
plug (F `* G) (inl (dfx , gx)) x = plug F dfx x , gx
plug (F `* G) (inr (fx , dgx)) x = fx , plug G dgx x

gulp : forall {X} F -> Fun F X -> Fun F (Fun (D F `* `X) X)
gulp {X} F = go F id where
  go : forall G -> (Fun (D G) X -> Fun (D F) X) ->
       Fun G X -> Fun G (Fun (D F `* `X) X)
  go `X wrap gx = wrap <> , gx
  go `0 wrap ()
  go `1 wrap <> = <>
  go (G `+ H) wrap (inl gx) = inl (go G (wrap o inl) gx)
  go (G `+ H) wrap (inr hx) = inr (go H (wrap o inr) hx)
  go (G `* H) wrap (gx , hx) = go G (\ z -> wrap (inl (z , hx))) gx ,
                                 go H (\ z -> wrap (inr (gx , z))) hx

mygulp = gulp (`X `* `X `* `X) (1 , 2 , 3)

data Desc (I : Set) : Set1 where
  `X : I -> Desc I
  `Sg : (S : Set)(T : S -> Desc I) -> Desc I
  `1 : Desc I
  _`*_ : (S T : Desc I) -> Desc I

Node : forall {I : Set} -> Desc I -> (I -> Set) -> Set
Node (`X i) X = X i
Node (`Sg S T) X = Sg S \ s -> Node (T s) X
Node (`1) X = One
Node (S `* T) X = Node S X * Node T X

data Data {I : Set}(F : I -> Desc I)(i : I) : Set where
  <_> : Node (F i) (Data F) -> Data F i

Two : Set
Two = One + One
pattern tt = inl <>
pattern ff = inr <>

NatD : One -> Desc One
NatD <> = `Sg Two \ 
  {  tt -> `1
  ;  ff -> `X <>
  }

NAT = Data NatD <>
-- zeD : NAT
pattern zeD = < tt , <> >
-- suD : NAT -> NAT
pattern suD n = < ff , n >

VecD : Set -> NAT -> Desc NAT
VecD A l =  `Sg Two \ 
  {  tt -> `Sg (zeD == l) \ _ -> `1
  ;  ff -> `Sg NAT \ n -> `Sg A \ a -> `X n `* `Sg (suD n == l) \ _ -> `1
  }

VEC : Set -> NAT -> Set
VEC A l = Data (VecD A) l
-- vnil : forall {A} -> VEC A zeD
pattern vnil = < tt , refl , <> >
-- vcons : forall {A n} -> A -> VEC A n -> VEC A (suD n)
pattern vcons a as = < ff , ._ , a , as , refl , <> >

vtail : forall {A n} -> VEC A (suD n) -> VEC A n
vtail < tt , () , <> >
vtail (vcons a as) = as

VecD' : Set -> NAT -> Desc NAT
VecD' A zeD = `1
VecD' A (suD n) = `Sg A \ _ -> `X n

VEC' : Set -> NAT -> Set
VEC' A l = Data (VecD' A) l

vtail' : forall {A n} -> VEC' A (suD n) -> VEC' A n
vtail' < a , as > = as

