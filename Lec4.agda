module Lec4 where

open import Basics

module Binding -- (E : Set) -- uncomment when introducing variables
  where

  {- The plan is to revisit Tuesday's construction of a "universe"
     of datatypes, given by a datatype of descriptions. But then,
     by adding some kind of "variables" and "binding", we'll extend
     this to a treatment of typed syntaxes. Simply typed lambda
     calculus is the key example to bear in mind.

     What makes a datatype a *syntax* is that it has a substitution
     structure, so we'll need to make sure that we can define a
     generic substitution operator. -}  -- C-s plum

  -- S
  -- P
  -- O
  -- I
  -- L
  -- E
  -- R
  -- S
  -- !








  {- uncomment when introducing variables
  data Cxt : Set where
    C0 : Cxt
    _:<_ : Cxt -> E -> Cxt
  infixl 3 _:<_

  data Var (V : E -> Set) : Cxt -> Set where
    top : forall {G e} -> V e -> Var V (G :< e)
    pop : forall {G e} -> Var V G -> Var V (G :< e)
  -}

  {- uncomment in case of an emergency
  data Ext : Set where
    E0 : Ext
    _:>_ : E -> Ext -> Ext
  infixr 3 _:>_

  _<><_ : Cxt -> Ext -> Cxt
  G <>< E0 = G
  G <>< (e :> E) = (G :< e) <>< E
  -}

  module Describing (I : Set) where  -- I is the set of permitted "sorts"

    {- E.g., for Nat, there is one sort. For Vec, the lengths are the
       sorts. For simply typed lambda calculus, the types are the sorts. -}

    data Desc : Set1 where
      `X     : I -> Desc
      `Sg    : (S : Set)(T : S -> Desc) -> Desc
      `0 `1  : Desc
      _`*_   : (S T : Desc) -> Desc
      -- and one more...

    Node : Desc -> (I ->                                       -- Cxt ->
                         Set) ->                               -- Cxt ->
                   Set                                  -- for C-s plum
    Node (`X i)      X  = X i
    Node (`Sg S T)   X  = Sg S \ s -> Node (T s) X
    Node `0          X  = Zero
    Node `1          X  = One
    Node (S `* T)    X  = Node S X * Node T X
    -- and one more...

    module Syntax
                                                     -- (V : I -> E -> Set)
             (F : I -> Desc)
             where

      data Term (i : I)                                      -- (G : Cxt)
                       : Set where -- I called this "Data" on Tuesday
        -- and one more
        <_> : Node (F i) Term  -> Term i

      -- visit the examples are at the end of the file (C-s banana)


      {- uncomment once we have contexts and variables
      Sub : Cxt -> Cxt -> Set
      Sub G D = forall {i} -> Var (V i) G -> Term i D

      Act : Cxt -> Cxt -> Set
      Act G D = forall {i} -> Term i G -> Term i D

      sub : forall {G D} -> Sub G D -> Act G D
      subNode : forall {G D} -> Sub G D -> (N : Desc) ->
         Node N Term G -> Node N Term D

      sub f (var x) = f x
      sub f {i} < t > = < subNode f (F i) t >
      subNode f N t = {!!}
      -}

      {- uncomment once we're shifty
      record Kit (K : I -> Cxt -> Set) : Set where
        constructor kit
        field
          kVa  : forall {i G}    -> Var (V i) G -> K i G
          kTm  : forall {i G}    -> K i G -> Term i G
          kWk  : forall {e i G}  -> K i G -> K i (G :< e)
        FunK : Cxt -> Cxt -> Set
        FunK G D = forall {i} ->  Var (V i) G -> K i D
        weak : forall {e G D} -> FunK G D -> FunK (G :< e) (D :< e)
        weak f x = ?
        kitSh : forall {G D} -> FunK G D -> Shub G D
        kitSh f X = ?
        act : forall {G D} -> FunK G D -> Act G D
        act = shub o kitSh
      open Kit public

      REN : Kit \ i G -> Var (V i) G
      REN = ?

      SUB : Kit TERM
      SUB = ?
      -}

    open Syntax public

  open Describing public

open Binding public

NoV : forall {I : Set} -> I -> Zero -> Set
NoV i ()




data NatE : Set where ze su : NatE  -- an enumeration, for readability
NatD : One -> Desc One
NatD <> = {!!}

NAT : Set
NAT = Term One NatD <>

-- rebuild the constructors

VecD : Set -> NAT -> Desc NAT
VecD A n  = {!!}

VEC : Set -> NAT -> Set
VEC A n = Term NAT (VecD A) n                            -- for C-s banana

-- example : VEC NatE < su , < su , < su , < ze , <> > > > >

data TyE : Set where nat arrow : TyE
TyD : One -> Desc One
TyD <> = `Sg TyE \
  {  nat    -> `1
  ;  arrow  -> `X <> `* `X <>
  }
pattern _>>_ s t = < arrow , s , t >
infixr 4 _>>_

TY : Set
TY = Term One TyD <>

-- Now, let's have variables. Go back to the top.

data LamC : Set where app lam : LamC

{- uncomment once we have variables
ULamD : One  -> Desc One One
ULamD <> = `Sg LamC \
  {  app  -> `X <> `* `X <>
  ;  lam  -> <> `=> `X <>
  }

ULam : Cxt One -> Set
ULam = Term One One (\ _ _ -> One) ULamD <>

myTerm : forall {G} -> ULam G
myTerm = ?
-}

{- uncomment once we have variables
TLamD : Ty -> Desc Ty Ty
TLamD t = `Sg LamC \
  {  lam -> ?
  ;  app -> ?
  }  -- where

_!-_ : Cxt Ty -> Ty -> Set
G !- t = Term Ty Ty _==_ TLamD t G
infixr 2 _!-_

-}