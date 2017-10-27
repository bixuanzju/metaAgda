module Containers where

open import Basics
open import Vect
open import Normal

record Con : Set₁ where
  constructor _◃_
  field
    Sh : Set
    Po : Sh → Set
  ⟦_⟧◃ : Set → Set
  ⟦_⟧◃ X = Σ[ s ∈ Sh ] (Po s → X)

open Con public
infixr 1 _◃_

K◃ : Set → Con
K◃ A = A ◃ (λ _ → Zero)

I◃ : Con
I◃ = One ◃ (λ _ → One)

_+◃_ : Con → Con → Con
(S ◃ P) +◃ (S' ◃ P') = (S ⊹ S') ◃ vv (P <?> P')

_×◃_ : Con → Con → Con
(S ◃ P) ×◃ (S' ◃ P') = (S × S') ◃ vv (λ s s' → P s ⊹ P' s')

Σ◃ : (A : Set) (C : A → Con) → Con
Σ◃ A C = (Σ A λ a → Sh (C a)) ◃ vv (λ a s → Po (C a) s)

Π◃ : (A : Set) (C : A → Con) → Con
Π◃ A C = ((a : A) → Sh (C a)) ◃ (λ f → Σ A (λ a → Po (C a) (f a)))

_∘◃_ : Con → Con → Con
(S ◃ P) ∘◃ C = Σ◃ S (λ s → Π◃ (P s) (λ p → C))

-- 3.1
instance
  conEndoFunctor : {C : Con} → EndoFunctor ⟦ C ⟧◃
  conEndoFunctor = record { map = λ f t → fst t , (λ x → f (snd t x)) }

conEndoFunctorOKP : {C : Con} → EndoFunctorOKP ⟦ C ⟧◃
conEndoFunctorOKP = record { endoFunctorId = λ t → refl
                           ; endoFunctorCo = λ f g x → refl
                           }

-- 3.2
conInj : ∀ {X} (F G : Con) → ⟦ F ⟧◃ X ⊹ ⟦ G ⟧◃ X → ⟦ F +◃ G ⟧◃ X
conInj F G (tt , shF , poF) = (tt , shF) , poF
conInj F G (ff , shG , poG) = (ff , shG) , poG

conPair : ∀ {X} (F G : Con) → ⟦ F ⟧◃ X × ⟦ G ⟧◃ X → ⟦ F ×◃ G ⟧◃ X
conPair F G ((shF , poF) , shG , poG) = (shF , shG) , (vv (poF <?> poG))

conΣ : ∀ {X} (A : Set) (C : A → Con) → (Σ A λ a → ⟦ C a ⟧◃ X) → ⟦ Σ◃ A C ⟧◃ X
conΣ A C (a , sh , p) = (a , sh) , p

conΠ : ∀ {X} (A : Set) (C : A → Con) → ((a : A) → ⟦ C a ⟧◃ X) → ⟦ Π◃ A C ⟧◃ X
conΠ A C t = (λ a → fst (t a)) , (λ x → snd (t (fst x)) (snd x))

con∘ : ∀ {X} (A B : Con) → (⟦ A ⟧◃ ∘ ⟦ B ⟧◃) X → ⟦ A ∘◃ B ⟧◃ X
con∘ A B (shA , poA) = (shA , (λ a → fst (poA a))) , (λ x → snd (poA (fst x)) (snd x))


_→◃_ : Con → Con → Set
(S ◃ P) →◃ (S' ◃ P') = Σ[ f ∈ (S → S') ] ((s : S) → P' (f s) → P s)

_/◃_ : ∀ {C C'} → C →◃ C' → ∀ {X} → ⟦ C ⟧◃ X → ⟦ C' ⟧◃ X
(to , fro) /◃ (s , k) = to s , k ∘ fro s

-- 3.3
morph◃ : ∀ {C C'} → (∀ {X} → ⟦ C ⟧◃ X → ⟦ C' ⟧◃ X) → C →◃ C'
morph◃ {C} f = (λ x → fst (f {Po C x} (x , id))) , (λ t x → snd (f {Po C t} (t , id)) x)

_→◃₂_ : Con → Con → Set
(S ◃ P) →◃₂ C = (s : S) → ⟦ C ⟧◃ (P s)

_/◃₂_ : ∀ {C C'} → C →◃₂ C' → ∀ {X} → ⟦ C ⟧◃ X → ⟦ C' ⟧◃ X
t /◃₂ (shC , poC) = fst (t shC) , (λ x → poC (snd (t shC) x))

morph◃₂ : ∀ {C C'} → (∀ {X} → ⟦ C ⟧◃ X → ⟦ C' ⟧◃ X) → C →◃₂ C'
morph◃₂ {C} f = λ s → fst (f {Po C s} (s , id)) , (λ x → snd (f {Po C s} (s , id)) x)

-- 3.4
id→◃ : ∀ {C} → C →◃ C
id→◃ = id , (λ _ → id)

_∘→◃_ : ∀ {C D E} → (D →◃ E) → (C →◃ D) → (C →◃ E)
(d2e , pd2e) ∘→◃ (c2d , pc2d) = (d2e ∘ c2d) , (λ s x → pc2d s (pd2e (c2d s) x))

data W (C : Con) : Set where
  <_> : ⟦ C ⟧◃ (W C) → W C

-- 3.5
NatW : Set
NatW = W (K◃ One +◃ I◃)

zeroW : NatW
zeroW = < (tt , <>) , (λ x → magic x) >

sucW : NatW → NatW
sucW n = < (ff , <>) , (λ x → n) >

precW : ∀ {l} {T : Set l} → T → (NatW → T → T) → NatW → T
precW z s < (tt , _) , _ > = z
precW z s < (ff , _) , p > = s (p _) z

addW : NatW → NatW → NatW
addW x y = precW y (λ _ z → sucW z) x

_ : addW zeroW (sucW zeroW) ≡ sucW zeroW
_ = refl

-- Fail on the base case, because Agda's equality is too weak?
-- indW : ∀ {l} (P : NatW → Set l) →
--          P zeroW →
--          ((n : NatW) → P n → P (sucW n)) →
--          (n : NatW) → P n
-- indW P z s < (tt , <>) , snd₂ > = {!z should fit here!}
-- indW P z s < (ff , <>) , p > =  s (p <>) (indW P z s (p <>))

_⋆_ : Con → Set → Set
C ⋆ X = W (K◃ X +◃ C)

-- 3.6
freeMonad : (C : Con) → Monad (_⋆_ C)
freeMonad C = record { return = ret ; _>>=_ = bind } where
  ret : {X : Set} → X → C ⋆ X
  ret x = < (tt , x) , (λ x → magic x) >
  bind : {S T : Set} → C ⋆ S → (S → C ⋆ T) → C ⋆ T
  bind < (tt , s) , p > f = f s
  bind < (ff , shC) , p > f = < (ff , shC) , (λ po → bind (p po) f) >

-- 3.7
_⋆◃ : Con → Con
_⋆◃ C = {!!}

-- 3.8
call : ∀ {C} → (s : Sh C) → C ⋆ Po C s
call s = {!!}
