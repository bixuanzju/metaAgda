module Basics where

open import Agda.Primitive

record One {l : Level} : Set l where
  constructor <>
open One public

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x
infix 1 _≡_
{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REFL     refl #-}

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

_∘_ : ∀ {i j k}
      {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k} ->
      (f : {a : A}(b : B a) -> C a b) ->
      (g : (a : A) -> B a) ->
      (a : A) -> C a (g a)
f ∘ g = \ a -> f (g a)

id : ∀ {k} {X : Set k} → X → X
id x = x

record Σ {l : Level}(S : Set l)(T : S -> Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Σ public

infix 2 Σ-syntax

Σ-syntax : ∀ {a} (A : Set a) → (A → Set a) → Set a
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

_×_ : {l : Level} -> Set l -> Set l -> Set l
S × T = Σ S \ _ -> T
infixr 4 _,_ _×_

vv_ :  ∀ {k l}{S : Set k}{T : S -> Set k}{P : Σ S T -> Set l} ->
       ((s : S)(t : T s) -> P (s , t)) ->
       (p : Σ S T) -> P p
(vv p) (s , t) = p s t
infixr 1 vv_

data Two : Set where tt ff : Two

_<?>_ : ∀ {l} {P : Two → Set l} → P tt → P ff → (b : Two) → P b
(t <?> f) tt = t
(t <?> f) ff = f

_⊹_ : Set → Set → Set
S ⊹ T = Σ Two (S <?> T)

data Zero : Set where

Dec : Set → Set
Dec X = X ⊹ (X → Zero)

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_ _-_
infixl 7 _*_

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

_-_ : ℕ → ℕ → ℕ
n     - zero = n
zero  - suc m = zero
suc n - suc m = n - m

_*_ : ℕ → ℕ → ℕ
zero  * m = zero
suc n * m = m + n * m

magic : Zero → {A : Set} → A
magic ()
