module Lec4 where

open import Basics

module Binding (E : Set) -- uncomment when introducing variables
  where

  {- The plan is to revisit Tuesday's construction of a "universe"
     of datatypes, given by a datatype of descriptions. But then,
     by adding some kind of "variables" and "binding", we'll extend
     this to a treatment of typed syntaxes. Simply typed lambda
     calculus is the key example to bear in mind.

     What makes a datatype a *syntax* is that it has a substitution
     structure, so we'll need to make sure that we can define a
     generic substitution operator. -}  -- C-s plum

  {- uncomment when introducing variables -}
  data Cxt : Set where
    C0 : Cxt
    _:<_ : Cxt -> E -> Cxt
  infixl 3 _:<_

  data Var (V : E -> Set) : Cxt -> Set where
    top : forall {G e} -> V e -> Var V (G :< e)
    pop : forall {G e} -> Var V G -> Var V (G :< e)
  {--}

  {- uncomment in case of an emergency -}
  data Ext : Set where
    E0 : Ext
    _:>_ : E -> Ext -> Ext
  infixr 3 _:>_

  _<><_ : Cxt -> Ext -> Cxt
  G <>< E0 = G
  G <>< (e :> E) = (G :< e) <>< E
  {--}

  module Describing (I : Set) where  -- I is the set of permitted "sorts"

    {- E.g., for Nat, there is one sort. For Vec, the lengths are the
       sorts. For simply typed lambda calculus, the types are the sorts. -}

    data Desc : Set1 where
      `X     : I -> Desc
      `Sg    : (S : Set)(T : S -> Desc) -> Desc
      `0 `1  : Desc
      _`*_   : (S T : Desc) -> Desc
      _`=>_  : E -> Desc -> Desc

    Node : Desc -> (I -> Cxt ->
                         Set) -> Cxt ->
                   Set                                  -- for C-s plum
    Node (`X i)      X  G = X i G
    Node (`Sg S T)   X  G = Sg S \ s -> Node (T s) X G
    Node `0          X  G = Zero
    Node `1          X  G = One
    Node (S `* T)    X  G = Node S X G * Node T X G
    Node (e `=> T)   X  G = Node T X (G :< e)

    module Syntax
             (V : I -> E -> Set)
             (F : I -> Desc)
             where

      data Term (i : I)(G : Cxt)
                       : Set where -- I called this "Data" on Tuesday
        var : Var (V i) G -> Term i G -- and one more
        <_> : Node (F i) Term G -> Term i G

      -- visit the examples are at the end of the file (C-s banana)


      {- uncomment once we have contexts and variables -}
      Shub : Cxt -> Cxt -> Set
      Shub G D = forall X {i} -> Var (V i) (G <>< X) -> Term i (D <>< X)

      Act : Cxt -> Cxt -> Set
      Act G D = forall {i} -> Term i G -> Term i D

      shub : forall {G D} -> Shub G D -> Act G D
      shubNode : forall {G D} -> Shub G D -> (N : Desc) ->
         Node N Term G -> Node N Term D

      shub f (var x) = f E0 x
      shub f {i} < t > = < shubNode f (F i) t >
      shubNode f (`X i) t = shub f t
      shubNode f (`Sg S T) (s , t) = s , shubNode f (T s) t
      shubNode f `0 ()
      shubNode f `1 <> = <>
      shubNode f (S `* T) (s , t) = shubNode f S s , shubNode f T t
      shubNode f (e `=> T) t = shubNode (f o _:>_ e) T t
      {--}

      {- uncomment once we're shifty -}
      record Kit (K : I -> Cxt -> Set) : Set where
        constructor kit
        field
          kVa  : forall {i G}    -> Var (V i) G -> K i G
          kTm  : forall {i G}    -> K i G -> Term i G
          kWk  : forall {e i G}  -> K i G -> K i (G :< e)
        FunK : Cxt -> Cxt -> Set
        FunK G D = forall {i} ->  Var (V i) G -> K i D
        weak : forall {e G D} -> FunK G D -> FunK (G :< e) (D :< e)
        weak f (top x) = kVa (top x)
        weak f (pop x) = kWk (f x)
        kitSh : forall {G D} -> FunK G D -> Shub G D
        kitSh f E0 = kTm o f
        kitSh f (e :> X) = kitSh (weak f) X
        act : forall {G D} -> FunK G D -> Act G D
        act = shub o kitSh
      open Kit public

      REN : Kit \ i G -> Var (V i) G
      REN = kit id var pop

      SUB : Kit Term
      SUB = kit var id (act REN pop)
      {--}

    open Syntax public

  open Describing public

open Binding public

NoV : forall {I : Set} -> I -> Zero -> Set
NoV i ()



data NatE : Set where ze su : NatE  -- an enumeration, for readability
NatD : One -> Desc Zero One
NatD <> = `Sg NatE (\
  { ze -> `1
  ; su -> `X <>
  })

NAT : Set
NAT = Term Zero One NoV NatD <> C0

-- rebuild the constructors
ZE : NAT
ZE = < ze , <> >

SU : NAT -> NAT
SU n = < su , n >

VecD : Set -> NAT -> Desc Zero NAT
VecD A (var ())
VecD A < ze , <> > = `1
VecD A < su , n > = `Sg A \ _ -> `X n

VEC : Set -> NAT -> Set
VEC A n = Term Zero NAT NoV (VecD A) n C0                           -- for C-s banana

--example : VEC NatE < su , < su , < su , < ze , <> > > > >
--example = {!-l!}

data TyE : Set where nat arrow : TyE
TyD : One -> Desc Zero One
TyD <> = `Sg TyE \
  {  nat    -> `1
  ;  arrow  -> `X <> `* `X <>
  }
pattern _>>_ s t = < arrow , s , t >
infixr 4 _>>_

TY : Set
TY = Term Zero One NoV TyD <> C0

-- Now, let's have variables. Go back to the top.

data LamC : Set where app lam : LamC

{- uncomment once we have variables -}
ULamD : One  -> Desc One One
ULamD <> = `Sg LamC \
  {  app  -> `X <> `* `X <>
  ;  lam  -> <> `=> `X <>
  }

ULam : Cxt One -> Set
ULam = Term One One (\ _ _ -> One) ULamD <>

--myTerm : forall {G} -> ULam G
--myTerm = {!-l!}
{--}

{- uncomment once we have variables -}
TLamD : TY -> Desc TY TY
TLamD t = `Sg LamC \
  {  app -> `Sg TY \ s -> `X (s >> t) `* `X s
  ;  lam -> lambody t
  }  where
  lambody : TY -> Desc TY TY
  lambody (var ())
  lambody < nat , <> > = `0
  lambody (s >> t) = s `=> `X t

_!-_ : Cxt TY -> TY -> Set
G !- t = Term TY TY _==_ TLamD t G
infixr 2 _!-_

{--}

example : forall {t} -> C0 !- t >> t
example = < lam , var (top refl) >