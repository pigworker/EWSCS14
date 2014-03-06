module CxData where

open import Basics

module Binding (E : Set) where

  data Cxt : Set where
    C0 : Cxt
    _:<_ : Cxt -> E -> Cxt
  infixl 3 _:<_

  data Ext : Set where
    E0 : Ext
    _:>_ : E -> Ext -> Ext
  infixr 3 _:>_

  _<><_ : Cxt -> Ext -> Cxt
  G <>< E0 = G
  G <>< (e :> E) = (G :< e) <>< E

  data Var (V : E -> Set) : Cxt -> Set where
    top : forall {G e} -> V e -> Var V (G :< e)
    pop : forall {G e} -> Var V G -> Var V (G :< e)

  module Describing (I : Set) where

    data Desc : Set1 where
      `X : I -> Desc
      `Sg : (S : Set)(T : S -> Desc) -> Desc
      `0 `1 : Desc
      _`*_ : (S T : Desc) -> Desc
      _`=>_ : E -> Desc -> Desc

    Node : Desc -> (I -> Cxt -> Set) -> Cxt -> Set
    Node (`X i) X G = X i G
    Node (`Sg S T) X G = Sg S \ s -> Node (T s) X G
    Node `0 X G = Zero
    Node `1 X G = One
    Node (S `* T) X G = Node S X G * Node T X G
    Node (e `=> T) X G = Node T X (G :< e)

    module Syntax (V : I -> E -> Set)(F : I -> Desc) where

      data Term (i : I)(G : Cxt) : Set where
        var : Var (V i) G -> Term i G
        <_> : Node (F i) Term G -> Term i G

      Shub : Cxt -> Cxt -> Set
      Shub G D = forall X {i} -> Var (V i) (G <>< X) -> Term i (D <>< X)

      Mor : Cxt -> Cxt -> Set
      Mor G D = forall {i} -> Term i G -> Term i D

      shub : forall {G D} -> Shub G D -> Mor G D
      shubNode : forall {G D} -> Shub G D -> (N : Desc) ->
         Node N Term G -> Node N Term D

      shub f (var x) = f E0 x
      shub f {i} < t > = < shubNode f (F i) t >
      shubNode f (`X x) t = shub f t
      shubNode f (`Sg S T) (s , t) = s , shubNode f (T s) t
      shubNode f `0 ()
      shubNode f `1 <> = <>
      shubNode f (N `* N') (n , n') = shubNode f N n , shubNode f N' n'
      shubNode f (e `=> N) t = shubNode (f o _:>_ e) N t

      exLaw : forall {G D}(f g : Shub G D)
              {i}(t : Term i G)
              (q : forall X {i} (x : Var (V i) (G <>< X)) -> f X x == g X x) ->
              shub f t == shub g t
      exLaw f g (var x) q = q E0 x
      exLaw f g {i} < t > q = cong <_> (exNodeLaw f g q (F i) t) where
        exNodeLaw : forall {G D}(f g : Shub G D)
         (q : forall X {i} (x : Var (V i) (G <>< X)) -> f X x == g X x) ->
         (N : Desc) -> (t : Node N Term G) ->
           shubNode f N t == shubNode g N t
        exNodeLaw f g q (`X i) x = exLaw f g x q
        exNodeLaw f g q (`Sg S T) (s , t) rewrite exNodeLaw f g q (T s) t = refl
        exNodeLaw f g q `0 ()
        exNodeLaw f g q `1 <> = refl
        exNodeLaw f g q (N `* N') (n , n')
          rewrite exNodeLaw f g q N n | exNodeLaw f g q N' n' = refl
        exNodeLaw f g q (e `=> N) t =
          exNodeLaw (f o _:>_ e) (g o _:>_ e) (q o _:>_ e) N t

      idSh : forall {G} -> Shub G G
      idSh X = var

      idLaw : forall {G}{i}(t : Term i G) -> shub idSh t == t
      idLaw (var x) = refl
      idLaw {G}{i} < t > = cong <_> (idNodeLaw (F i) t) where
        idNodeLaw : forall {G} -> (N : Desc) -> (t : Node N Term G) ->
          shubNode idSh N t == t
        idNodeLaw (`X i) x = idLaw x
        idNodeLaw (`Sg S T) (s , t) rewrite idNodeLaw (T s) t = refl
        idNodeLaw `0 ()
        idNodeLaw `1 <> = refl
        idNodeLaw (N `* N') (n , n')
          rewrite idNodeLaw N n | idNodeLaw N' n' = refl
        idNodeLaw (x `=> N) t = idNodeLaw N t

      shSh : forall {G D} -> Shub G D -> (X : Ext) -> Shub (G <>< X) (D <>< X)
      shSh f E0 = f
      shSh f (e :> X) = shSh (f o _:>_ e) X

      coSh : forall {G D H} -> Shub D H -> Shub G D -> Shub G H
      coSh dh gd X x = shub (shSh dh X) (gd X x)

      coLaw : forall {G D H}(dh : Shub D H)(gd : Shub G D)
        {i}(t : Term i G) -> shub dh (shub gd t) == shub (coSh dh gd) t
      coLaw dh gd (var x) = refl
      coLaw {G}{D}{H} dh gd {i} < t > = cong <_> (coNodeLaw dh gd (F i) t) where
        coNodeLaw : forall {G D H}(dh : Shub D H)(gd : Shub G D)
          (N : Desc) -> (t : Node N Term G) ->
          shubNode dh N (shubNode gd N t) == shubNode (coSh dh gd) N t
        coNodeLaw dh gd (`X j) t = coLaw dh gd t
        coNodeLaw dh gd (`Sg S T) (s , t) rewrite coNodeLaw dh gd (T s) t = refl
        coNodeLaw dh gd `0 ()
        coNodeLaw dh gd `1 <> = refl
        coNodeLaw dh gd (N `* N') (n , n')
          rewrite coNodeLaw dh gd N n | coNodeLaw dh gd N' n' = refl
        coNodeLaw dh gd (e `=> N) t = coNodeLaw (dh o _:>_ e) (gd o _:>_ e) N t
      
      record Kit (K : I -> Cxt -> Set) : Set where
        constructor kit
        field
          kVa  : forall {i G} -> Var (V i) G -> K i G
          kTm  : forall {i G} -> K i G -> Term i G
          kWk  : forall {e i G} -> K i G -> K i (G :< e)
          kTmVa : forall {i G}(x : Var (V i) G) -> kTm (kVa x) == var x
          kWkVa : forall {e i G}(x : Var (V i) G) ->
            kWk {e} (kVa x) == kVa (pop x)
        MorK : Cxt -> Cxt -> Set
        MorK G D = forall {i} ->  Var (V i) G -> K i D
        weak : forall {e G D} -> MorK G D -> MorK (G :< e) (D :< e)
        weak f (top x) = kVa (top x)
        weak f (pop x) = kWk (f x)
        exWeak : forall {G D e}(f g : MorK G D) ->
          (q : forall {i}(x : Var (V i) G) -> f x == g x) ->
          forall {i}(x : Var (V i) (G :< e)) -> weak f x == weak g x
        exWeak f g q (top x) = refl
        exWeak f g q (pop x) = cong kWk (q x)
        kitSh : forall {G D} -> MorK G D -> Shub G D
        kitSh f E0        = kTm o f
        kitSh f (e :> X)  = kitSh (weak f) X
        act : forall {G D} -> MorK G D -> Mor G D
        act = shub o kitSh
        exKitSh : forall {G D}(f g : MorK G D)
          X {i} (x : Var (V i) (G <>< X))
          (q : forall {i}(x : Var (V i) G) -> f x == g x) ->
          kitSh f X x == kitSh g X x
        exKitSh f g E0 x q = cong kTm (q x)
        exKitSh f g (e :> X) x q = exKitSh (weak f) (weak g) X x (exWeak f g q)
        idKitSh : forall {G}(f : MorK G G)
          X {i}(x : Var (V i) (G <>< X))
          (q : forall {i}(x : Var (V i) G) -> f x == kVa x) ->
            kitSh f X x == idSh X x
        idKitSh f E0        x q = trans (cong kTm (q x)) (kTmVa x)
        idKitSh f (e :> X)  x q = idKitSh (weak f) X x (\
          {  (top x)  -> refl
          ;  (pop x)  -> trans (cong kWk (q x)) (kWkVa x)
          })
        idKitLaw : forall {G}{i}(t : Term i G) ->
          act kVa t == t
        idKitLaw t =
          act kVa t
            =!! exLaw (kitSh kVa) idSh t
                (\ X x -> idKitSh kVa X x (\ _ -> refl) ) >>
          shub idSh t =!! idLaw t >>
          t <QED>
      open Kit

      REN : Kit (Var o V)
      REN = record
        {  kVa = id
        ;  kTm = var
        ;  kWk = pop
        ;  kTmVa = \ _ -> refl
        ;  kWkVa = \ _ -> refl
        }

      SUB : Kit Term
      SUB = record
        {  kVa = var
        ;  kTm = id
        ;  kWk = act REN pop
        ;  kTmVa = \ _ -> refl
        ;  kWkVa = \ _ -> refl
        }

      module ComposeWeaken
        {K1 K2 K3}(KIT1 : Kit K1)(KIT2 : Kit K2)(KIT3 : Kit K3)
        (co : forall {G D H} ->
               (dh : MorK KIT1 D H)(gd : MorK KIT2 G D) -> MorK KIT3 G H)
        (tm : forall {G D H}
               (dh : MorK KIT1 D H)(gd : MorK KIT2 G D)
               {i}(x : Var (V i) G) ->
               act KIT1 dh (kTm KIT2 (gd x)) == kTm KIT3 (co dh gd x))
        (wkt : forall {e G D H}
               (dh : MorK KIT1 D H)(gd : MorK KIT2 G D){i}(x : V i e) ->
               co (weak KIT1 dh) (weak KIT2 gd) (top x) == kVa KIT3 (top x))
        (wkp : forall {e G D H}
               (dh : MorK KIT1 D H)(gd : MorK KIT2 G D){i}
                     (x : Var (V i) G) ->
               co (weak KIT1 {e} dh) (weak KIT2 gd) (pop x)
                     == kWk KIT3 (co dh gd x)) where
        coWkLemma : forall {G D H}(dh : MorK KIT1 D H)(gd : MorK KIT2 G D)
          X {i}(x : Var (V i) (G <>< X)) ->
          coSh (kitSh KIT1 dh) (kitSh KIT2 gd) X x == kitSh KIT3 (co dh gd) X x
        coWkLemma dh gd E0 x = tm dh gd x
        coWkLemma dh gd (e :> X) x =
          coSh (kitSh KIT1 (weak KIT1 dh)) (kitSh KIT2 (weak KIT2 gd)) X x
            =!! coWkLemma (weak KIT1 dh) (weak KIT2 gd) X x >>
          kitSh KIT3 (co (weak KIT1 dh) (weak KIT2 gd)) X x
            =!! exKitSh KIT3 (co (weak KIT1 dh) (weak KIT2 gd))
                  (weak KIT3 (co dh gd)) X x
                (\ { (top x) -> wkt dh gd x ; (pop x) -> wkp dh gd x }) >>
          kitSh KIT3 (weak KIT3 (co dh gd)) X x <QED>
        coWkAct : forall {G D H}(dh : MorK KIT1 D H)(gd : MorK KIT2 G D)
          {i}(t : Term i G) ->
          act KIT1 dh (act KIT2 gd t) == act KIT3 (co dh gd) t
        coWkAct dh gd t =
          act KIT1 dh (act KIT2 gd t)
            =!! coLaw (kitSh KIT1 dh) (kitSh KIT2 gd) t >>
          shub (coSh (kitSh KIT1 dh) (kitSh KIT2 gd)) t
            =!! exLaw  (coSh (kitSh KIT1 dh) (kitSh KIT2 gd))
                 (kitSh KIT3 (co dh gd)) t (coWkLemma dh gd) >>
          act KIT3 (co dh gd) t <QED>
      open ComposeWeaken        

      preRen : forall {K}(KIT : Kit K){G D H}
        (dh : MorK KIT D H)(gd : MorK REN G D)
        {i}(t : Term i G) -> act KIT dh (act REN gd t) == act KIT (dh o gd) t
      preRen KIT = coWkAct KIT REN KIT (\ f g x -> f (g x))
        (\ _ _ _ -> refl) (\ _ _ _ -> refl) (\ _ _ _ -> refl)

      record KitCo {K}(KIT : Kit K) : Set where
        constructor kitCo
        field
          kBi : forall {G D} -> MorK KIT G D -> forall {i} -> K i G -> K i D
          kBiVa : forall {G D}(f : MorK KIT G D){i}(x : Var (V i) G) ->
            kBi f (kVa KIT x) == f x
          kBiTm : forall {G D}(f : MorK KIT G D){i}(k : K i G) ->
            kTm KIT (kBi f k) == act KIT f (kTm KIT k)
          kBiWk : forall {G D e}(f : MorK KIT G D){i}(k : K i G) ->
            kWk KIT {e} (kBi f k) == kBi (weak KIT f) (kWk KIT k)
        kCo : forall {G D H} -> MorK KIT D H -> MorK KIT G D -> MorK KIT G H
        kCo dh gd = kBi dh o gd
        coKitSh : forall {G D H}
           (dh : MorK KIT D H)(gd : MorK KIT G D)(gh : MorK KIT G H)
           X {i}(x : Var (V i) (G <>< X))
           (q : forall {i}(x : Var (V i) G) -> gh x == kCo dh gd x) ->
           kitSh KIT gh X x == coSh (kitSh KIT dh) (kitSh KIT gd) X x
        coKitSh dh gd gh E0 x q =
          kTm KIT (gh x)                 =!! cong (kTm KIT) (q x) >>
          kTm KIT (kBi dh (gd x))        =!! kBiTm dh (gd x) >>
          act KIT dh (kTm KIT (gd x))    <QED>
        coKitSh dh gd gh (e :> X) x q =
          coKitSh (weak KIT dh) (weak KIT gd) (weak KIT gh) X x (\
            {  (top x) -> 
               kVa KIT (top x)           << kBiVa (weak KIT dh) (top x) !!=
               kBi (weak KIT dh) (kVa KIT (top x))                    <QED>
            ;  (pop x) ->
               kWk KIT (gh x)                      =!! cong (kWk KIT) (q x) >>
               kWk KIT (kBi dh (gd x))             =!! kBiWk dh (gd x) >>
               kBi (weak KIT dh) (kWk KIT (gd x))  <QED>
            })
        coKitLaw :  forall {G D H}
          (dh : MorK KIT D H)(gd : MorK KIT G D){i}(t : Term i G) ->
          act KIT dh (act KIT gd t) == act KIT (kCo dh gd) t
        coKitLaw = coWkAct KIT KIT KIT kCo
          (\ dh gd t -> act KIT dh (kTm KIT (gd t))
             << kBiTm dh (gd t) !!= kTm KIT (kCo dh gd t) <QED>)
          (\ dh gd x -> kBiVa (weak KIT dh) (top x))
          (\ dh gd x -> kBi (weak KIT dh) (kWk KIT (gd x))
             << kBiWk dh (gd x) !!= kWk KIT (kCo dh gd x) <QED>)

      open KitCo

      RENCO : KitCo REN
      RENCO = record
        {  kBi = id
        ;  kBiVa = \ _ _ -> refl
        ;  kBiTm = \ _ _ -> refl
        ;  kBiWk = \ _ _ -> refl
        }

      renSub : forall {G D H}(dh : MorK REN D H)(gd : MorK SUB G D)
        {i}(t : Term i G) ->
        act REN dh (act SUB gd t) == act SUB (act REN dh o gd) t
      renSub = coWkAct REN SUB SUB (\ dh gd -> act REN dh o gd)
                 (\ _ _ _ -> refl) (\ _ _ _ -> refl)
                 \ dh gd x ->
                   act REN (weak REN dh) (act REN pop (gd x))
                     =!! preRen REN (weak REN dh) pop (gd x) >>
                   act REN (pop o dh) (gd x)
                     << preRen REN pop dh (gd x) !!=
                   act REN pop (act REN dh (gd x)) <QED>

      SUBCO : KitCo SUB
      SUBCO = record
        {  kBi = act SUB
        ;  kBiVa = \ _ _ -> refl
        ;  kBiTm = \ _ _ -> refl
        ;  kBiWk = \ f k ->
           act REN pop (act SUB f k) =!! renSub pop f k >>
           act SUB (act REN pop o f) k << preRen SUB (weak SUB f) pop k !!=
           act SUB (weak SUB f) (act REN pop k) <QED>
        }

    open Syntax public

  open Describing public

open Binding public

data Constr : Set where lam app : Constr

ULamD : One -> Desc One One
ULamD <> = `Sg Constr \
  {  lam -> <> `=> `X <>
  ;  app -> `X <> `* `X <>
  }

ULam : Cxt One -> Set
ULam = Term One One (\ _ _ -> One) ULamD <>

myTerm : forall {G} -> ULam G
myTerm = < lam , < lam , < lam ,
  < app , < app , var (pop (pop (top <>))) , var (top <>) > ,
    < app , var (pop (top <>)) , var (top <>) > > > > >

data Ty : Set where
  base : Ty
  _>>_ : Ty -> Ty -> Ty
infixr 3 _>>_

TLamD : Ty -> Desc Ty Ty
TLamD t = `Sg Constr \
  {  lam -> body t
  ;  app -> `Sg Ty \ s -> `X (s >> t) `* `X s
  }  where
  body : Ty -> Desc Ty Ty
  body base = `0
  body (s >> t) = s `=> `X t

_!-_ : Cxt Ty -> Ty -> Set
G !- t = Term Ty Ty _==_ TLamD t G
infixr 2 _!-_

tyS : forall {G g s t} -> G !- (g >> s >> t) >> (g >> s) >> (g >> t)
tyS = < lam , < lam , < lam ,
  < app , _ , < app , _ , var (pop (pop (top refl))) , var (top refl) > ,
    < app , _ , var (pop (top refl)) , var (top refl) > > > > >
