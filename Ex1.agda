module Ex1 where

open import Basics

_+N_ : Nat -> Nat -> Nat
ze +N y = y
su x +N y = su (x +N y)

_+N'_ : Nat -> Nat -> Nat
ze +N' y = y
su x +N' y = x +N' su y


{- 1.1 See how it works proving this lemma by inspecting the goals,
   then removing the comments left-to-right one-by-one -}

lemma+N' : forall x y -> su x +N' y == su (x +N' y)
lemma+N' ze y = refl
lemma+N' (su x) y rewrite lemma+N' x (su y) = refl


{- 1.2 Check that you can use "rewrite" to push vector concatenation
   through, despite choosing the awkward addition. -}

_++_ : forall {m n X} -> Vec X m -> Vec X n -> Vec X (m +N n)
[] ++ ys        = ys
(x , xs) ++ ys  = x , xs ++ ys

_++'_ : forall {m n X} -> Vec X m -> Vec X n -> Vec X (m +N' n)
xs ++' ys = {!!}


{- 1.3 Chop a vector in two. Note how "with" lets us grab more information
   to a pattern match. -}

chop : forall m {n X} -> Vec X (m +N n) -> Vec X m * Vec X n
chop ze      xs        = {!!}
chop (su m)  (x , xs)  with  chop m xs
chop (su m)  (x , xs)  |     ys , zs    = {!!}


{- Recall zapp and vec -}

zapp : forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
zapp [] [] = []
zapp (f , fs) (s , ss) = f s , zapp fs ss

vec : forall {n X} -> X -> Vec X n
vec {ze} x = []
vec {su n} x = x , vec x


{- 1.4 One-liners, using zapp and vec -}

vmap : forall {n S T} -> (S -> T) -> Vec S n -> Vec T n
vmap f ss = {!!}

_+V_ : forall {n} -> Vec Nat n -> Vec Nat n -> Vec Nat n
xs +V ys = {!!}

vzip : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
vzip ss ts = {!!}


{- here is vector traversal -}

vtrav : forall
          (F : Set -> Set)
          (pure  : forall {X} -> X -> F X)
          (_$_   : forall {S T} -> F (S -> T) -> F S -> F T)
          {n S T} -> (S -> F T) -> Vec S n -> F (Vec T n)
vtrav F pure _$_ f []        = pure []
vtrav F pure _$_ f (s , ss)  = (pure _,_ $ f s) $ vtrav F pure _$_ f ss


{- 1.6 vector map bis -}

vmap' : forall {n S T} -> (S -> T) -> Vec S n -> Vec T n
vmap' = vtrav {!!} {!!} {!!}


{- 1.7 vector total -}

vtotal : forall {n S T} -> Vec Nat n -> Nat
vtotal = vtrav {!!} {!!} {!!} {!!}


{- 1.8 scalar product -}

_*N_ : Nat -> Nat -> Nat
x *N y = {!!}

_*V_ : forall {n} -> Vec Nat n -> Vec Nat n -> Nat
xs *V ys = {!!}


{- matrices -}

Matrix : Set -> Nat * Nat -> Set
Matrix X (r , c) = Vec (Vec X r) c  -- a row of columns


{- 1.9 vector transposition (a one-liner) -}

vxpose : forall {m n X} -> Matrix X (m , n) -> Matrix X (n , m)
vxpose = {!!}


{- 1.10 matrix multiplication -}

_*M_ :  forall {l m n} ->
        Matrix Nat (l , m) -> Matrix Nat (m , n) -> Matrix Nat (l , n)
lm *M mn = {!!}


{- riffling -}

data Riffle : Nat -> Nat -> Nat -> Set where
  ze : Riffle ze ze ze
  ll : forall {x y z} -> Riffle x y z -> Riffle (su x) y (su z)
  rr : forall {x y z} -> Riffle x y z -> Riffle x (su y) (su z)


{- 1.11 interleave according to a riffle -}

vriffle :  forall {x y z S T} -> Riffle x y z ->
           Vec S x -> Vec T y -> Vec (S + T) z
vriffle r ss ts = {!!}


{- 1.12 show that every vector of choices can be expressed as a riffle -}

data IsRiffle {z S T} : Vec (S + T) z -> Set where
  byRiffle :  forall {x y}(r : Riffle x y z)(ss : Vec S x)(ts : Vec T y) ->
              IsRiffle (vriffle r ss ts)

isRiffle : forall {z S T}(xs : Vec (S + T) z) -> IsRiffle xs
isRiffle xs = {!!}
