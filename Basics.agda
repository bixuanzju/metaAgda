module Basics where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Data.Product


record One {l : Level} : Set l where
  constructor <>
open One public

subst : ∀ {k l} {X : Set k} {s t : X} → s ≡ t → (P : X → Set l) → P s → P t
subst refl P p = p

_≡⟨_⟩_  : ∀ {l} {X : Set l} (x : X) {y z} → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ refl ⟩ q = q

_⟨_⟩≡_ : ∀ {l} {X : Set l} (x : X) {y z} → y ≡ x → y ≡ z → x ≡ z
_ ⟨ refl ⟩≡ q = q

⟨⟩_ : ∀ {l} {X : Set l} {x y : X} → x ≡ y → y ≡ x
⟨⟩ refl = refl

_□ : ∀ {l} {X : Set l} (x : X) → x ≡ x
x □ = refl

infixr 1 _≡⟨_⟩_ _⟨_⟩≡_ _□

cong : ∀ {k l} {X : Set k} {Y : Set l} (f : X → Y) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

data Two : Set where tt ff : Two

_<?>_ : ∀ {l} {P : Two → Set l} → P tt → P ff → (b : Two) → P b
(t <?> f) tt = t
(t <?> f) ff = f

_⊹_ : Set → Set → Set
S ⊹ T = Σ Two (S <?> T)

data Zero : Set where

Dec : Set → Set
Dec X = X ⊹ (X → Zero)
