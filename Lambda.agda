module Lambda where

open import Agda.Builtin.List
open import Basics

data ⋆ : Set where
  ι : ⋆
  _▹_ : ⋆ → ⋆ → ⋆
infixr 5 _▹_

data Cx (X : Set) : Set where
  ε : Cx X
  _,,_ : Cx X → X → Cx X
infixl 4 _,,_


data _∈_ (τ : ⋆) : Cx ⋆ → Set where
  zero : ∀ {Γ} → τ ∈ Γ ,, τ
  suc : ∀ {Γ σ} → τ ∈ Γ → τ ∈ Γ ,, σ
infix 3 _∈_

data _⊢_ (Γ : Cx ⋆) : ⋆ → Set where
  var : ∀ {τ}
        → τ ∈ Γ
        ----------
        → Γ ⊢ τ

  lam : ∀ {σ τ}
        → Γ ,, σ ⊢ τ
        --------------
        → Γ ⊢ σ ▹ τ

  app : ∀ {σ τ}
        → Γ ⊢ σ ▹ τ
        → Γ ⊢ σ
        --------------
        → Γ ⊢ τ

infix 3 _⊢_

⟦_⟧T : ⋆ → Set
⟦ ι ⟧T = ℕ
⟦ σ ▹ τ ⟧T = ⟦ σ ⟧T → ⟦ τ ⟧T

⟦_⟧C : Cx ⋆ → (⋆ → Set) → Set
⟦ ε ⟧C V = One
⟦ Γ ,, σ ⟧C V = ⟦ Γ ⟧C V × V σ

⟦_⟧V : ∀ {Γ τ V} → τ ∈ Γ → ⟦ Γ ⟧C V → V τ
⟦ zero ⟧V (γ , t) = t
⟦ suc i ⟧V (γ , s) = ⟦ i ⟧V γ

⟦_⟧ₜ : ∀ {Γ τ} → Γ ⊢ τ → ⟦ Γ ⟧C ⟦_⟧T → ⟦ τ ⟧T
⟦ var x ⟧ₜ γ = ⟦ x ⟧V γ
⟦ lam t ⟧ₜ γ = λ x → ⟦ t ⟧ₜ (γ , x)
⟦ app f s ⟧ₜ γ = ⟦ f ⟧ₜ γ (⟦ s ⟧ₜ γ)

-- Type-preserving mappings from variables in Γ to variables/terms in Δ
Ren Sub : Cx ⋆ → Cx ⋆ → Set
Ren Γ Δ = ∀ {τ} → τ ∈ Γ → τ ∈ Δ
Sub Γ Δ = ∀ {τ} → τ ∈ Γ → Δ ⊢ τ

-- Context extension
_<><_ : ∀ {X} → Cx X → List X → Cx X
xz <>< [] = xz
xz <>< (x ∷ xs) = xz ,, x <>< xs
infixl 4 _<><_

-- Shiftable substitution
Shub : Cx ⋆ → Cx ⋆ → Set
Shub Γ Δ = ∀ Ξ → Sub (Γ <>< Ξ) (Δ <>< Ξ)

_//_ : ∀ {Γ Δ} (θ : Shub Γ Δ) {τ} → Γ ⊢ τ → Δ ⊢ τ
θ // var x = θ [] x
θ // lam t = lam ((λ Ξ t → θ (_ ∷ Ξ) t) // t)
θ // app f s = app (θ // f) (θ // s)

wkr : ∀ {Γ Δ σ} → Ren Γ Δ → Ren (Γ ,, σ) (Δ ,, σ)
wkr r zero = zero
wkr r (suc t) = suc (r t)

ren : ∀ {Γ Δ} → Ren Γ Δ → Shub Γ Δ
ren r [] = var ∘ r
ren r (_ ∷ Ξ) = ren (wkr r) Ξ

wks : ∀ {Γ Δ σ} → Sub Γ Δ → Sub (Γ ,, σ) (Δ ,, σ)
wks s zero = var zero
wks s (suc t) = ren suc // s t

sub : ∀ {Γ Δ} → Sub Γ Δ → Shub Γ Δ
sub s [] = s
sub s (x ∷ Ξ) = sub (wks s) Ξ

weak : ∀ {Γ} Ξ → Ren Γ (Γ <>< Ξ)
weak [] i = i
weak (_ ∷ Ξ) i = weak Ξ (suc i)


_<>>_ : ∀ {X} → Cx X → List X → List X
ε <>> ys = ys
(xz ,, x) <>> ys = xz <>> (x ∷ ys)
infixl 4 _<>>_

lem : ∀ {X} (Δ Γ : Cx X) Ξ →
      (Δ <>> []) ≡ (Γ <>> Ξ) → (Γ <>< Ξ) ≡ Δ
lem Δ Γ Ξ q = {!!}

lambda : ∀ {Γ σ τ} →
         ((∀ {Δ Ξ} {{_ : (Δ <>> []) ≡ (Γ <>> σ ∷ Ξ)}} → Δ ⊢ σ) →
           Γ ,, σ ⊢ τ) →
         Γ ⊢ σ ▹ τ
lambda {Γ} f = lam (f λ {Δ Ξ} {{q}} → subst (lem Δ Γ (_ ∷ Ξ) q) (λ Γ₁ → Γ₁ ⊢ _) (var (weak Ξ zero)))

myTest : ε ⊢ (ι ▹ ι) ▹ (ι ▹ ι)
myTest = lambda λ f → lambda (λ x → app (f {{refl}}) (app (f {{refl}}) (x {{refl}})))

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

