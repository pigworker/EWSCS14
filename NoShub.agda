module NoShub where

open import Basics

flip : forall {R S : Set}{T : Set} -> (R -> S -> T) -> S -> R -> T
flip f s r = f r s

module Binding (E : Set) where

  data Cxt : Set where
    C0 : Cxt
    _:<_ : Cxt -> E -> Cxt
  infixl 3 _:<_

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

    _>>>_ : (P Q : I -> Cxt -> Set) -> Set
    P >>> Q = forall {G i} -> P i G -> Q i G
    infixr 4 _>>>_
    _/_ : (P : I -> Cxt -> Set) -> E -> I -> Cxt -> Set
    (P / e) i G = P i (G :< e)
    infixl 5 _/_
    [_>_]_~_ : forall (P Q : I -> Cxt -> Set){G D : Cxt}
          (f g : forall {i} -> P i G -> Q i D) -> Set
    [ P > Q ] f ~ g = forall {i} x -> f {i} x == g {i} x
    infixr 4 [_>_]_~_

    module Syntax (V : I -> E -> Set)(F : I -> Desc) where

      VAR = Var o V

      data Term (i : I)(G : Cxt) : Set where
        var : Var (V i) G -> Term i G
        <_> : Node (F i) Term G -> Term i G

      Act : Cxt -> Cxt -> Set
      Act G D = forall {i} -> Term i G -> Term i D
      
      record Kit (K : I -> Cxt -> Set) : Set where
        constructor kit
        field
          kVa  : VAR >>> K
          kTm  : K >>> Term
          kWk  : forall {e} -> K >>> K / e
          kTmVa : forall {G} -> [ VAR > Term ] (kTm o kVa {G}) ~ var
          kWkVa : forall {e G} -> [ VAR > K ] (kWk {e} o kVa {G}) ~ (kVa o pop)

        FunK : Cxt -> Cxt -> Set
        FunK G D = forall {i} ->  Var (V i) G -> K i D

        weak : forall {e G D} -> FunK G D -> FunK (G :< e) (D :< e)
        weak f (top x) = kVa (top x)
        weak f (pop x) = kWk (f x)

        exWeak : forall {e G D}(f g : FunK G D) ->
          [ VAR > K ] f ~ g -> [ VAR > K ] weak {e} f ~ weak g
        exWeak f g q (top x) = refl
        exWeak f g q (pop x) = cong kWk (q x)

        idWeak : forall {e G}(f : FunK G G) ->
          [ VAR > K ] f ~ kVa -> [ VAR > K ] weak {e} f ~ kVa
        idWeak f q (top x) = refl
        idWeak f q (pop x) =
          kWk (f x) =!! cong kWk (q x) >>
          kWk (kVa x) =!! kWkVa x >>
          kVa (pop x) <QED>

        act : forall {G D} -> FunK G D -> Act G D
        actNode : forall {G D} -> FunK G D -> (N : Desc) ->
           Node N Term G -> Node N Term D
        act f (var x) = kTm (f x)
        act f {i} < t > = < actNode f (F i) t >
        actNode f (`X x) t = act f t
        actNode f (`Sg S T) (s , t) = s , actNode f (T s) t
        actNode f `0 ()
        actNode f `1 <> = <>
        actNode f (N `* N') (n , n') = actNode f N n , actNode f N' n'
        actNode f (e `=> N) t = actNode (weak f) N t

        exAct : forall {G D}(f g : FunK G D) ->
                [ VAR > K ] f ~ g -> [ Term > Term ] act f ~ act g
        exActNode : forall {G D}(f g : FunK G D) -> ([ VAR > K ] f ~ g) -> 
          (N : Desc) -> (t : Node N Term G) ->
          actNode f N t == actNode g N t
        exAct f g q (var x) = cong kTm (q x)
        exAct f g q {i} < t > = cong <_> (exActNode f g q (F i) t)
        exActNode f g q (`X i) t = exAct f g q t
        exActNode f g q (`Sg S T) (s , t) =
          cong (_,_ s) (exActNode f g q (T s) t)
        exActNode f g q `0 ()
        exActNode f g q `1 <> = refl
        exActNode f g q (S `* T) (s , t) =
          actNode f S s , actNode f T t
            =!! cong (_,_ (actNode f S s)) (exActNode f g q T t) >>
          actNode f S s , actNode g T t
            =!! cong (flip _,_ (actNode g T t)) (exActNode f g q S s) >>
          actNode g (S `* T) (s , t) <QED>
        exActNode f g q (x `=> T) t
          = exActNode (weak f) (weak g) (exWeak f g q) T t

        idAct : forall {G}(f : FunK G G) ->
                [ VAR > K ] f ~ kVa -> [ Term > Term ] act f ~ id
        idActNode : forall {G}(f : FunK G G) -> ([ VAR > K ] f ~ kVa) -> 
          (N : Desc) -> (t : Node N Term G) ->
          actNode f N t == t
        idAct f q (var x) =
          kTm (f x) =!! cong kTm (q x) >> kTm (kVa x) =!! kTmVa x >> var x <QED>
        idAct f q {i} < t > = cong <_> (idActNode f q (F i) t)
        idActNode f q (`X i) t = idAct f q t
        idActNode f q (`Sg S T) (s , t) =
          cong (_,_ s) (idActNode f q (T s) t)
        idActNode f q `0 ()
        idActNode f q `1 <> = refl
        idActNode f q (S `* T) (s , t) =
          actNode f S s , actNode f T t
            =!! cong (_,_ (actNode f S s)) (idActNode f q T t) >>
          actNode f S s , t
            =!! cong (flip _,_ t) (idActNode f q S s) >>
          s , t <QED>
        idActNode f q (x `=> T) t =
          idActNode (weak f) (idWeak f q) T t

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
        (kk : forall {G D H} ->
              (dh : FunK KIT1 D H)(gd : FunK KIT2 G D) -> FunK KIT3 G H)
        (tm : forall {G D H}(dh : FunK KIT1 D H)(gd : FunK KIT2 G D) ->
              [ VAR > Term ]
              act KIT1 dh o kTm KIT2 o gd ~ kTm KIT3 o kk dh gd)
        (wkt : forall {e G D H}
               (dh : FunK KIT1 D H)(gd : FunK KIT2 G D){i}(x : V i e) ->
               kk (weak KIT1 dh) (weak KIT2 gd) (top x) == kVa KIT3 (top x))
        (wkp : forall {e G D H}(dh : FunK KIT1 D H)(gd : FunK KIT2 G D) ->
               [ VAR > K3 ]
               kk (weak KIT1 {e} dh) (weak KIT2 gd) o pop ~ kWk KIT3 o kk dh gd)
        where
        kkAct : forall {G D H}(dh : FunK KIT1 D H)(gd : FunK KIT2 G D) ->
          [ Term > Term ] act KIT1 dh o act KIT2 gd ~ act KIT3 (kk dh gd)
        kkActNode : forall {G D H}(dh : FunK KIT1 D H)(gd : FunK KIT2 G D)
          (N : Desc) -> (t : Node N Term G) ->
          actNode KIT1 dh N (actNode KIT2 gd N t) == actNode KIT3 (kk dh gd) N t
        kkAct dh gd (var x) = tm dh gd x
        kkAct dh gd {i} < t > = cong <_> (kkActNode dh gd (F i) t) 
        kkActNode dh gd (`X i) t = kkAct dh gd t
        kkActNode dh gd (`Sg S T) (s , t) =
          cong (_,_ s) (kkActNode dh gd (T s)t)
        kkActNode dh gd `0 ()
        kkActNode dh gd `1 <> = refl
        kkActNode dh gd (S `* T) (s , t) =
          actNode KIT1 dh S (actNode KIT2 gd S s) ,
          actNode KIT1 dh T (actNode KIT2 gd T t)
            =!! cong (_,_ (actNode KIT1 dh S (actNode KIT2 gd S s)))
                (kkActNode dh gd T t) >>
          actNode KIT1 dh S (actNode KIT2 gd S s) , actNode KIT3 (kk dh gd) T t
            =!! cong (flip _,_ (actNode KIT3 (kk dh gd) T t))
                 (kkActNode dh gd S s) >>
          actNode KIT3 (kk dh gd) S s , actNode KIT3 (kk dh gd) T t
            <QED>
        kkActNode dh gd (x `=> T) t =
          actNode KIT1 (weak KIT1 dh) T (actNode KIT2 (weak KIT2 gd) T t)
            =!! kkActNode (weak KIT1 dh) (weak KIT2 gd) T t >>
          actNode KIT3 (kk (weak KIT1 dh) (weak KIT2 gd)) T t
            =!! exActNode KIT3
                  (kk (weak KIT1 dh) (weak KIT2 gd)) (weak KIT3 (kk dh gd))
                  (\ { (top x) -> wkt dh gd x ; (pop x) -> wkp dh gd x })
                  T t >>
          actNode KIT3 (weak KIT3 (kk dh gd)) T t
            <QED>

      open ComposeWeaken        

      preRen : forall {K}(KIT : Kit K){G D H}
        (dh : FunK KIT D H)(gd : FunK REN G D)
        {i}(t : Term i G) -> act KIT dh (act REN gd t) == act KIT (dh o gd) t
      preRen KIT = kkAct KIT REN KIT (\ f g x -> f (g x))
        (\ _ _ _ -> refl) (\ _ _ _ -> refl) (\ _ _ _ -> refl)

      record KitCo {K}(KIT : Kit K) : Set where
        constructor kitCo
        field
          kBi : forall {G D} -> FunK KIT G D -> forall {i} -> K i G -> K i D
          kBiVa : forall {G D}(f : FunK KIT G D) ->
            [ VAR > K ] kBi f o kVa KIT ~ f
          kBiTm : forall {G D}(f : FunK KIT G D) ->
            [ K > Term ] kTm KIT o kBi f ~ act KIT f o kTm KIT
          kBiWk : forall {G D e}(f : FunK KIT G D) ->
            [ K > K ] kWk KIT {e} o kBi f ~ kBi (weak KIT f) o kWk KIT
        kCo : forall {G D H} -> FunK KIT D H -> FunK KIT G D -> FunK KIT G H
        kCo dh gd = kBi dh o gd
        coAct :  forall {G D H}(dh : FunK KIT D H)(gd : FunK KIT G D) ->
          [ Term > Term ] act KIT dh o act KIT gd ~ act KIT (kCo dh gd)
        coAct = kkAct KIT KIT KIT kCo
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

      renSub : forall {G D H}(dh : FunK REN D H)(gd : FunK SUB G D)
        {i}(t : Term i G) ->
        act REN dh (act SUB gd t) == act SUB (act REN dh o gd) t
      renSub = kkAct REN SUB SUB (\ dh gd -> act REN dh o gd)
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
