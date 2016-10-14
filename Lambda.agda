module Lambda where

open import Data.Nat
open import Data.Product
open import Data.List

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

Ren Sub : Cx ⋆ → Cx ⋆ → Set
Ren Γ Δ = ∀ {τ} → τ ∈ Γ → τ ∈ Δ
Sub Γ Δ = ∀ {τ} → τ ∈ Γ → Δ ⊢ τ

_<><_ : ∀ {X} → Cx X → List X → Cx X
xz <>< [] = xz
xz <>< (x ∷ xs) = xz ,, x <>< xs
infixl 4 _<><_

Shub : Cx ⋆ → Cx ⋆ → Set
Shub Γ Δ = ∀ Ξ → Sub (Γ <>< Ξ) (Δ <>< Ξ)

_//_ : ∀ {Γ Δ} (θ : Shub Γ Δ) {τ} → Γ ⊢ τ → Δ ⊢ τ
θ // var x = θ [] x
θ // lam t = lam ((λ Ξ → θ (_ ∷ Ξ)) // t)
θ // app f s = app (θ // f) (θ // s)
