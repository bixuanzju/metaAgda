module MetaAgda where

open import Data.Nat
open import Data.Product hiding (zip; map) renaming (uncurry to ̌)
open import Function using (_∘_; id)
open import Data.Unit using (⊤)

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

test : Vec ℕ 2
test = ((λ x → x + 1) , (λ x → x + 2) , <>) ⊗ (1 , 2 , <>)

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
  infixr 4 _·_
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
transpose vs = traverse (\s → s) vs

test2 : Vec (Vec ℕ 3) 2
test2 = (1 , 2 , 3 , <>) , (4 , 5 , 6 , <>) , <>

crush : ∀ {F X Y} {{TF : Traversable F}} {{M : Monoid Y}} →
          (X → Y) → F X → Y
crush {{M = M}} = traverse {T = ⊤} {{AG = monoidApplicative {{M}}}}

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

-- Ex 1.12
_+ℕ_ : ℕ → ℕ → ℕ
zero +ℕ y = y
suc x +ℕ y = suc (x +ℕ y)

_×ℕ_ : ℕ → ℕ → ℕ
zero ×ℕ y = zero
suc x ×ℕ y = y +ℕ (x ×ℕ y)

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
VecN n = ⊤ / pure n

ListN : Normal
ListN = ℕ / id

Kₙ : Set → Normal
Kₙ A = A / λ _ → 0

IKₙ : Normal
IKₙ = VecN 1

_+ₙ_ : Normal → Normal → Normal
(ShF / szF) +ₙ (ShG / scG) = (ShF ⊹ ShG) / ̌ (szF <?> scG)

_×ₙ_ : Normal → Normal → Normal
(ShF / szF) ×ₙ (ShG / scG) = (ShF × ShG) / ̌ (λ f g → szF f +ℕ scG g)

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
_++_ : ∀ {m n X} → Vec X m → Vec X n → Vec X (m +ℕ n)
<> ++ ys = ys
(x , xs) ++ ys = x , xs ++ ys

nPair : ∀ {X} (F G : Normal) → ⟦ F ⟧ X × ⟦ G ⟧ X → ⟦ F ×ₙ G ⟧ X
nPair F G ((ShF , xsF) , ShG , xsG) = (ShF , ShG) , (xsF ++ xsG)

vSplit : ∀ {X n} m → Vec X (m +ℕ n) → Vec X m × Vec X n
vSplit zero vs = <> , vs
vSplit (suc m) (x , vs) with vSplit m vs
vSplit (suc m) (x , vs) | xs , ys = (x , xs) , ys

-- Why the following doesn't work?
-- nSurj : ∀ {X} F G (s : ⟦ F ×ₙ G ⟧ X) → Image nPair F G ∋ s
-- nSurj F G ((ShF , ShG) , xs) with vSplit (size F ShF) xs
-- nSurj F G ((ShF , ShG) , xs) | xsF , xsG = from ((ShF , xsF) , ShG , xsG)

-- Ex 1.14
listNMonoid : {X : Set} → Monoid (⟦ ListN ⟧ X)
listNMonoid {X} = record { ε = zero , <> ; _·_ = h }
  where h : ⟦ ListN ⟧ X → ⟦ ListN ⟧ X → ⟦ ListN ⟧ X
        h (n , xs) (m , ys) = (n +ℕ m) , (xs ++ ys)

sumMonoid : Monoid ℕ
sumMonoid = record { ε = zero ; _·_ = _+ℕ_ }

normalTraversable : (F : Normal) → Traversable ⟦ F ⟧
normalTraversable F =
  record { traverse = λ {{aG}} f → ̌ (λ s xs → pure {{aG}} (_,_ s) ⊗ traverse f xs) }

_∘ₙ_ : Normal → Normal → Normal
F ∘ₙ (ShG / szG) = (⟦ F ⟧ ShG) / crush {{normalTraversable F}} szG
