module MetaAgda where

open import Data.Nat
open import Data.Product hiding (zip; map)
open import Function using (_∘_)

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
  monadVec = record {return = vec; _>>=_  = λ vs fs →  diag (vmap fs vs)}

applicativeVec₂ : ∀ {n} → Applicative λ X → Vec X n
applicativeVec₂ = monadApplicative

test : Vec ℕ 2
test = ((λ x → x + 1) , (λ x → x + 2) , <>) ⊗ (1 , 2 , <>)
