module MetaAgda where

open import Data.Nat
open import Data.Product hiding (zip; map; swap)
open import Function using (_∘_; id)
open import Agda.Builtin.Equality


data Vec (X : Set) : ℕ → Set where
  <> : Vec X zero
  _,_ : {n : ℕ} → X → Vec X n → Vec X (suc n)

zip : ∀ {n S T} → Vec S n → Vec T n → Vec (S × T) n
zip <> <> = <>
zip (x , ss) (x₁ , tt) = (x , x₁) , zip ss tt

-- Ex 1.1
vec : ∀ {n X} → X → Vec X n
vec {zero} x = <>
vec {suc n} x = x , vec x

-- Ex 1.2
vapp : ∀ {n S T} → Vec (S → T) n → Vec S n → Vec T n
vapp <> <> = <>
vapp (x , fs) (x₁ , ss) = x x₁ , vapp fs ss

-- Ex 1.3
vmap : ∀ {n S T} → (S → T) → Vec S n → Vec T n
vmap f ss = vapp (vec f) ss

-- Ex 1.4
zip₂ : ∀ {n S T} → Vec S n → Vec T n → Vec (S × T) n
zip₂ ss ts = vapp (vmap _,_ ss) ts

-- Ex 1.5
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

proj : ∀ {n X} → Vec X n → Fin n → X
proj <> ()
proj (x , xs) zero = x
proj (x , xs) (suc i) = proj xs i

tabulate : ∀ {n X} → (Fin n → X) → Vec X n
tabulate {zero} f = <>
tabulate {suc n} f = f zero , tabulate (λ s → f (suc s))

record EndoFunctor (F : Set → Set) : Set₁ where
  field
    map : ∀ {S T} → (S → T) → F S → F T

open EndoFunctor {{...}} public

record Applicative (F : Set → Set) : Set₁ where
  infixl 2 _⊗_
  field
    pure : ∀ {X} → X → F X
    _⊗_ : ∀ {S T} → F (S → T) → F S → F T
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record { map = _⊗_ ∘ pure }

open Applicative {{...}} public

instance
  applicativeVec : ∀ {n} → Applicative λ X → Vec X n
  applicativeVec = record {pure = vec; _⊗_ = vapp}

instance
  endoFunctorVec : ∀ {n} → EndoFunctor λ X → Vec X n
  endoFunctorVec = applicativeEndoFunctor

instance
  applicativeFun : ∀ {S} → Applicative λ X → S → X
  applicativeFun = record {pure = λ x s → x ; _⊗_ = λ f a s → f s (a s)}

record Monad (F : Set → Set) : Set₁ where
  field
    return : ∀ {X} → X → F X
    _>>=_ : ∀ {S T} → F S → (S → F T) → F T
  monadApplicative : Applicative F
  monadApplicative =
    record {pure = return; _⊗_ = λ ff fs → ff >>= λ f → fs >>= λ s → return (f s)}

open Monad {{...}} public


-- Ex 1.6
tl : ∀ {X n} → Vec X (suc n) → Vec X n
tl (x , xs) = xs

diag : ∀ {T n} → Vec (Vec T n) n → Vec T n
diag <> = <>
diag ((x , vs) , vs₁) =  x , diag (vmap tl vs₁)

instance
  monadVec : {n : ℕ} → Monad λ X → Vec X n
  monadVec = record {return = vec; _>>=_  = λ vs fs → diag (vmap fs vs)}

applicativeVec₂ : ∀ {n} → Applicative λ X → Vec X n
applicativeVec₂ = monadApplicative

-- Ex 1.7
instance
  applicativeId : Applicative id
  applicativeId = record {pure = id; _⊗_ = λ f x → f x}

applicativeComp : ∀ {F G} → Applicative F → Applicative G → Applicative (F ∘ G)
applicativeComp aF aG =
  record {pure =  (pure {{aF}}) ∘ ((pure {{aG}}))
         ;_⊗_ = λ fs ts → _⊗_ {{aF}} (_⊗_ {{aF}} (pure {{aF}} (_⊗_ {{aG}})) fs) ts}

-- Ex 1.8
record Monoid (X : Set) : Set where
  infixr 5 _·_
  field
    ε : X
    _·_ : X → X → X
  monoidApplicative : Applicative λ _ → X
  monoidApplicative = record {pure = λ _ → ε; _⊗_ = _·_}
open Monoid {{...}} public

instance
  ℕ-monoid : Monoid ℕ
  ℕ-monoid = record {ε = 0; _·_ = _+_}

-- Ex 1.9
-- What is point-wise product?

record Traversable (F : Set → Set) : Set₁ where
  field
    traverse : ∀ {G S T} {{AG : Applicative G}} →
                 (S → G T) → F S → G (F T)
  traversableEndoFunctor : EndoFunctor F
  traversableEndoFunctor = record {map = traverse}
open Traversable {{...}} public

instance
  traversableVec : {n : ℕ} → Traversable λ X → Vec X n
  traversableVec = record {traverse = vtr} where
    vtr : ∀ {n G S T} {{_ : Applicative G}} →
            (S → G T) → Vec S n → G (Vec T n)
    vtr {{aG}} f <> = pure {{aG}} <>
    vtr {{aG}} f (v , vs) =  pure {{aG}} _,_ ⊗ f v ⊗ vtr f vs

-- Ex 1.10
transpose : ∀ {m n X} → Vec (Vec X n) m → Vec (Vec X m) n
transpose vs = traverse id vs

data One : Set where <> : One

crush : ∀ {F X Y} {{TF : Traversable F}} {{M : Monoid Y}} →
          (X → Y) → F X → Y
crush {{M = M}} = traverse {T = One} {{AG = monoidApplicative {{M}}}}

test3 : ℕ
test3 = crush {F = λ X → Vec X 2} ( λ x → x + 1) (1 , 2 , <>)

-- Ex 1.11
traversableId : Traversable id
traversableId = record {traverse = λ f x → f x}

traversableComp : ∀ {F G} → Traversable F → Traversable G → Traversable (F ∘ G)
traversableComp tF tG = record {traverse = λ f fgs → (traverse {{tF}} (λ gs → traverse {{tG}} f gs) fgs)}

data Two : Set where tt ff : Two

_<?>_ : ∀ {l} {P : Two → Set l} → P tt → P ff → (b : Two) → P b
(t <?> f) tt = t
(t <?> f) ff = f

_⊹_ : Set → Set → Set
S ⊹ T = Σ Two (S <?> T)

record Normal : Set₁ where
  constructor _/_
  field
    Shape : Set
    size : Shape → ℕ
  ⟦_⟧ : Set → Set
  ⟦_⟧ X = Σ Shape λ s → Vec X (size s)
open Normal public
infixr 0 _/_

VecN : ℕ → Normal
VecN n = One / pure n

ListN : Normal
ListN = ℕ / id

Kₙ : Set → Normal
Kₙ A = A / λ _ → 0

IKₙ : Normal
IKₙ = VecN 1

_+ₙ_ : Normal → Normal → Normal
(ShF / szF) +ₙ (ShG / scG) = (ShF ⊹ ShG) / uncurry (szF <?> scG)

_×ₙ_ : Normal → Normal → Normal
(ShF / szF) ×ₙ (ShG / scG) = (ShF × ShG) / uncurry (λ f g → szF f + scG g)

nInj : ∀ {X} (F G : Normal) → ⟦ F ⟧ X ⊹ ⟦ G ⟧ X → ⟦ F +ₙ G ⟧ X
nInj F G (tt , ShF , xs) = (tt , ShF) , xs
nInj F G (ff , ShG , xs) = (ff , ShG) , xs

data Image_∋_ {A B : Set} (f : A → B) : B → Set where
  from : (x : A) → Image f ∋ f x

nCase : ∀ {X} F G (s : ⟦ F +ₙ G ⟧ X) → Image nInj F G ∋ s
nCase F G ((tt , ShF) , xs) = from (tt , ShF , xs)
nCase F G ((ff , ShG) , xs) = from (ff , ShG , xs)

nOut : ∀ {X} (F G : Normal) → ⟦ F +ₙ G ⟧ X → ⟦ F ⟧ X ⊹ ⟦ G ⟧ X
nOut F G xs' with nCase F G xs'
nOut F G .(nInj F G x) | from x = x

-- Ex 1.13
_++_ : ∀ {m n X} → Vec X m → Vec X n → Vec X (m + n)
<> ++ ys = ys
(x , xs) ++ ys = x , xs ++ ys

nPair : ∀ {X} (F G : Normal) → ⟦ F ⟧ X × ⟦ G ⟧ X → ⟦ F ×ₙ G ⟧ X
nPair F G ((ShF , xsF) , ShG , xsG) = (ShF , ShG) , (xsF ++ xsG)

vSplit : ∀ m n {X} (xs : Vec X (m + n)) → Image (uncurry (_++_ {m}{n}{X})) ∋ xs
vSplit zero n xs = from (<> , xs)
vSplit (suc m) n (x , xs) with vSplit m n xs
vSplit (suc m) n (x , .(y ++ ys)) | from (y , ys) = from ((x , y) , ys)

nSurj : ∀ {X} F G (s : ⟦ F ×ₙ G ⟧ X) → Image nPair F G ∋ s
nSurj F G ((shF , shG) , xs) with vSplit (size F shF) (size G shG) xs
nSurj F G ((shF , shG) , .(xs ++ ys)) | from (xs , ys) = from ((shF , xs) , (shG , ys))

-- Ex 1.14
instance
  listNMonoid : {X : Set} → Monoid (⟦ ListN ⟧ X)
  listNMonoid {X} = record { ε = zero , <> ; _·_ = h }
    where h : ⟦ ListN ⟧ X → ⟦ ListN ⟧ X → ⟦ ListN ⟧ X
          h (n , xs) (m , ys) = (n + m) , (xs ++ ys)

sumMonoid : Monoid ℕ
sumMonoid = record { ε = zero ; _·_ = _+_ }

normalTraversable : (F : Normal) → Traversable ⟦ F ⟧
normalTraversable F =
  record { traverse = λ {{aG}} f → uncurry (λ s xs → pure {{aG}} (_,_ s) ⊗ traverse f xs) }

_∘ₙ_ : Normal → Normal → Normal
F ∘ₙ (ShG / szG) = (⟦ F ⟧ ShG) / crush {{normalTraversable F}} szG

sizeT : ∀ {F} {{TF : Traversable F}} {X} → F X → ℕ
sizeT = crush (λ _ → 1)

normalT : ∀ F {{TF : Traversable F}} → Normal
normalT F = (F One) / sizeT

shapeT : ∀ {F} {{TF : Traversable F}} {X} → F X → F One
shapeT = traverse (λ _ → <>)

one : ∀ {X} → X → ⟦ ListN ⟧ X
one x = 1 , (x , <>)

-- Extract its context, put them in a vector, along with the size
contextT : ∀ {F} {{TF : Traversable F}} {X} → F X → ⟦ ListN ⟧ X
contextT = crush one

-- Ex 1.15
_→ₙ_ : Normal → Normal → Set
F →ₙ G = (s : Shape F) → ⟦ G ⟧ (Fin (size F s))

nMorph : ∀ {F G} → F →ₙ G → ∀ {X} → ⟦ F ⟧ X → ⟦ G ⟧ X
nMorph f (s , xs) with f s
nMorph f (s , xs) | s' , is = s' , map (proj xs) is


-- tabulate id generate a vector with elements of its own indexes
morphN : ∀ {F G} → (∀ {X} → ⟦ F ⟧ X → ⟦ G ⟧ X) → F →ₙ G
morphN {F} f s with f (s , tabulate id)
morphN {F} f s | sh , xs = sh , xs

-- Ex 1.16
_⊜_ : Normal → Normal → Normal
(ShF / szF) ⊜ (ShG / szG) = ShF × ShG / uncurry (λ f g → szF f * szG g)

tomato : ∀ m n {X} → Vec X (m * n) → Vec (Vec X n) m
tomato zero n xs = <>
tomato (suc m) n xs with vSplit n (m * n) xs
tomato (suc m) n .(xs ++ ys) | from (xs , ys) = xs , tomato m n ys

otamot : ∀ m n {X} → Vec (Vec X n) m → Vec X (m * n)
otamot zero n <> = <>
otamot (suc n) m (xs , xss) = xs ++ otamot n m xss

swap : (F G : Normal) → (F ⊜ G) →ₙ (G ⊜ F)
swap F G (shF , shG) = (shG , shF) , otamot (size G shG) (size F shF) (transpose (tomato (size F shF) (size G shG) (tabulate id)))

subst : ∀ {k l} {X : Set k} {s t : X} → s ≡ t → (P : X → Set l) → P s → P t
subst refl P p = p

drop : (F G : Normal) → (F ⊜ G) →ₙ (F ∘ₙ G)
drop F G (shF , shG) = (shF , (vec shG)) , subst (help (size F shF)) (Vec _) (tabulate id) where
  help : ∀ n → (n * size G shG) ≡ crush (size G) (vec {n} shG)
  help zero = refl
  help (suc n) rewrite help n = refl


record MonoidOk X {{M : Monoid X}} : Set where
  field
    absorbL : (x : X) → ε · x ≡ x
    absorbR : (x : X) → x · ε ≡ x
    assoc   : (x y z : X) → (x · y) · z ≡ x · (y · z)

_+zero : ∀ x → x + zero ≡ x
zero +zero = refl
suc x +zero rewrite x +zero = refl

assoc+ : ∀ x y z → (x + y) + z ≡ x + (y + z)
assoc+ zero y z = refl
assoc+ (suc x) y z rewrite assoc+ x y z = refl

natMonoidOK : MonoidOk ℕ
natMonoidOK = record
  { absorbL = λ _ → refl
  ; absorbR = _+zero
  ; assoc = assoc+
  }


listNMonoidOK : {X : Set} → MonoidOk (⟦ ListN ⟧ X)
listNMonoidOK {X} = record
  { absorbL = λ _ → refl
  ; absorbR =  uncurry aR
  ; assoc = uncurry aa
  } where
  aR : ∀ n (xs : Vec X n) → (n , xs) · ε {{listNMonoid}} ≡ (n , xs)
  aR zero <> = refl
  aR (suc n) (x , xs) = subst (aR n xs)
                          (uncurry (λ m ys → (suc (n + 0) , x , (xs ++ <>)) ≡ (suc m , x , ys))) refl
  aa : ∀ n (xs : Vec X n) (ys zs : ⟦ ListN ⟧ X) →
       ((n , xs) · ys) · zs ≡ (n , xs) · (ys · zs)
  aa zero <> ys zs = refl
  aa (suc n) (x , xs) (i , ys) (j , zs) =
    subst (aa n xs (i , ys) (j , zs)) (uncurry (λ m ms → _≡_ {_} {⟦ ListN ⟧ X} (suc (n + i + j) , (x , ((xs ++ ys) ++ zs))) (suc m , (x , ms)))) refl

-- Ex 1.18
-- I cannot even write the type because _≡_ requires the types of the arguments syntactically equal.

record MonoidHom {X} {{MX : Monoid X}} {Y} {{MY : Monoid Y}} (f : X → Y) : Set where
  field
    respε : f ε ≡ ε
    resp· : ∀ x x' → f (x · x') ≡ f x · f x'

fstHom : ∀ {X} → MonoidHom {⟦ ListN ⟧ X} {ℕ} proj₁
fstHom = record { respε = refl ; resp· = λ _ _ → refl }

_=̇_ : ∀ {l} {S : Set l} {T : S → Set l} (f g : (x : S) → T x) → Set l
f =̇ g = ∀ x → f x ≡ g x
infix 1 _=̇_

record EndoFunctorOKP F {{FF : EndoFunctor F}} : Set₁ where
  field
    endoFunctorId : ∀ {X} → map {{FF}} {X} id =̇ id
    endoFunctorCo : ∀ {R S T} (f : S → T) (g : R → S) →
                    map {{FF}} f ∘ map g =̇ map (f ∘ g)

-- Ex 1.19
vecEndoFunctorOKP : ∀ {n} → EndoFunctorOKP λ X → Vec X n
vecEndoFunctorOKP = record { endoFunctorId = vappid ; endoFunctorCo = vappco } where
  vappid : ∀ {X n} → (x : Vec X n) → vapp (vec id) x ≡ x
  vappid <> = refl
  vappid (x , xs) rewrite vappid xs = refl
  vappco : ∀ {n R S T} → (f : S → T) (g : R → S) (x : Vec R n) →
           vapp (vec f) (vapp (vec g) x) ≡ vapp (vec (λ s → f (g s))) x
  vappco f g <> = refl
  vappco f g (x , xs) rewrite vappco f g xs = refl
