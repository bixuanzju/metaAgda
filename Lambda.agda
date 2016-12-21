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
θ // lam t = lam ((λ l x → θ (_ ∷ l) x) // t)
θ // app f s = app (θ // f) (θ // s)

wkr : ∀ {Γ Δ σ} → Ren Γ Δ → Ren (Γ ,, σ) (Δ ,, σ)
wkr r zero = zero
wkr r (suc t) = suc (r t)

ren : ∀ {Γ Δ} → Ren Γ Δ → Shub Γ Δ
ren r [] = λ x → var (r x)
ren r (_ ∷ Ξ) = λ x → ren (wkr r) Ξ x

wks : ∀ {Γ Δ σ} → Sub Γ Δ → Sub (Γ ,, σ) (Δ ,, σ)
wks s zero = var zero
wks s (suc t) = ren suc // (s t)

sub : ∀ {Γ Δ} → Sub Γ Δ → Shub Γ Δ
sub s [] = s
sub s (_ ∷ Ξ) = sub (wks s) Ξ

weak : ∀ {Γ} Ξ → Ren Γ (Γ <>< Ξ)
weak [] i = i
weak (_ ∷ Ξ) i = weak Ξ (suc i)

lambda' : ∀ {Γ σ τ} → ((∀ {Ξ} → Γ ,, σ <>< Ξ ⊢ σ) → Γ ,, σ ⊢ τ) → Γ ⊢ σ ▹ τ
lambda' f = lam (f (λ {Ξ} → var (weak Ξ zero)))

_<>>_ : ∀ {X} → Cx X → List X → List X
ε <>> ys = ys
(xz ,, x) <>> ys = xz <>> (x ∷ ys)
infixl 4 _<>>_


lem2 : ∀ {X} → (xs ys : List X) → (Γ : Cx X) → xs ≡ Γ <>> ys → Γ <>< ys ≡ ε <>< xs
lem2 xs ys ε q rewrite q = refl
lem2 xs ys (Γ ,, y) q = lem2 xs (y ∷ ys) Γ q


lem1 : ∀ {X} → (Δ Γ : Cx X) → (xs ys : List X) → Δ <>> xs ≡ Γ <>> ys → Γ <>< ys ≡ Δ <>< xs
lem1 ε Γ xs ys q = lem2 xs ys Γ q
lem1 (Δ ,, x) Γ xs ys q = lem1 Δ Γ (x ∷ xs) ys q


-- Ex 2.1
lem : ∀ {X} (Δ Γ : Cx X) Ξ →
      (Δ <>> []) ≡ (Γ <>> Ξ) → (Γ <>< Ξ) ≡ Δ
lem Δ Γ Ξ q = lem1 Δ Γ [] Ξ q

lambda : ∀ {Γ σ τ} → ((∀ {Δ Ξ} {{_ : (Δ <>> []) ≡ (Γ <>> σ ∷ Ξ)}} → Δ ⊢ σ) → Γ ,, σ ⊢ τ) → Γ ⊢ σ ▹ τ
lambda {Γ} f = lam (f (λ {Δ Ξ} {{q}} → subst (lem Δ Γ (_ ∷ Ξ) q) (λ Γ₁ → Γ₁ ⊢ _) (var (weak Ξ zero))))

-- Why?
_ : ε ⊢ (ι ▹ ι) ▹ ι ▹ ι
_ = lambda λ f → lambda λ x → app (f {{refl}}) (app (f {{refl}}) (x {{refl}}))

mutual
  -- Normal forms
  data _⊨_ (Γ : Cx ⋆) : ⋆ → Set where
    lam : ∀ {σ τ} → Γ ,, σ ⊨ τ → Γ ⊨ σ ▹ τ
    _$_ : ∀ {τ} → τ ∈ Γ → Γ ⊨* τ → Γ ⊨ ι

  -- Spines
  data _⊨*_ (Γ : Cx ⋆) : ⋆ → Set where
    <> : Γ ⊨* ι
    _,_ : ∀ {τ σ} → Γ ⊨ σ → Γ ⊨* τ → Γ ⊨* σ ▹ τ

infix 3 _⊨_ _⊨*_
infix 3 _$_

-- Ex 2.2
_-×_ : ∀ (Γ : Cx ⋆) {τ} (x : τ ∈ Γ) → Cx ⋆
ε -× ()
(Γ ,, y) -× zero = Γ
(Γ ,, y) -× suc x = Γ -× x ,, y

_≠_ : ∀ {Γ σ} (x : σ ∈ Γ) → Ren (Γ -× x) Γ
zero ≠ y = suc y
suc x ≠ zero = zero
suc x ≠ suc y = suc (x ≠ y)

data Veq? {Γ σ} (x : σ ∈ Γ) : ∀ {τ} → τ ∈ Γ → Set where
  same : Veq? x x
  diff : ∀ {τ} (y : τ ∈ Γ -× x) → Veq? x (x ≠ y)

-- Ex 2.3
veq? : ∀ {Γ σ τ} (x : σ ∈ Γ) (y : τ ∈ Γ) → Veq? x y
veq? zero zero = same
veq? zero (suc y) = diff y
veq? (suc x) zero = diff zero
veq? (suc x) (suc y) with veq? x y
veq? (suc x) (suc .x) | same = same
veq? (suc x) (suc .(x ≠ y)) | diff y = diff (suc y)

-- Ex 2.4
mutual
  renNm : ∀ {Γ Δ τ} → Ren Γ Δ → Γ ⊨ τ → Δ ⊨ τ
  renNm r (lam t) = lam (renNm (wkr r) t)
  renNm r (x $ sp) = r x $ renSp r sp
  renSp : ∀ {Γ Δ τ} → Ren Γ Δ → Γ ⊨* τ → Δ ⊨* τ
  renSp r <> = <>
  renSp r (s , ss) = renNm r s , renSp r ss

-- Ex 2.5
mutual
  <_/_>_ : ∀ {Γ σ τ} → (x : σ ∈ Γ) → Γ -× x ⊨ σ → Γ ⊨ τ → Γ -× x ⊨ τ
  < x / s > lam t = lam (< suc x / renNm suc s > t)
  < x / s > (r $ ss) with veq? x r
  < x / s > (.x $ ss) | same = s $$ (< x / s >* ss)
  < x / s > (.(x ≠ y) $ ss) | diff y =  y $ (< x / s >* ss)

  <_/_>*_ : ∀ {Γ σ τ} → (x : σ ∈ Γ) → Γ -× x ⊨ σ → Γ ⊨* τ → Γ -× x ⊨* τ
  < x / s >* <> = <>
  < x / s >* (t , ts) = (< x / s > t) , < x / s >* ts

  _$$_ : ∀ {Γ τ} → Γ ⊨ τ → Γ ⊨* τ → Γ ⊨ ι
  f $$ <> = f
  lam f $$ (s , ss) = (< zero / s > f) $$ ss


-- Ex 2.6
eta-long : ∀ {Γ σ} (x : σ ∈ Γ) t → (∀ {Δ} → Ren Γ Δ → Δ ⊨* t → Δ ⊨* σ) → Γ ⊨ t
eta-long x ι f = x $ f id <>
eta-long x (t₁ ▹ t₂) f = lam (eta-long (suc x) t₂ (λ rho ss → f (rho ∘ suc) (eta-long (rho zero) t₁ (λ _ → id) , ss)))

normalize : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊨ τ
normalize (var x) = eta-long x _ (λ _ → id)
normalize (lam t) = lam (normalize t)
normalize (app f s) with normalize f | normalize s
normalize (app f s) | lam f' | s' = < zero / s' > f'

wkTm : ∀ {Γ τ σ} → (x : τ ∈ Γ) → Γ -× x ⊢ σ → Γ ⊢ σ
wkTm x (var y) = var (x ≠ y)
wkTm x (lam t) = lam (wkTm (suc x) t)
wkTm x (app t₁ t₂) = app (wkTm x t₁) (wkTm x t₂)

-- Another way to represent normal forms, better for my understanding
-- mutual
--   data Nf : Cx ⋆ → ⋆ → Set where
--     λn : ∀ {Γ σ τ} → Nf (Γ ,, σ) τ → Nf Γ (σ ▹ τ)
--     ne : ∀ {Γ} → Ne Γ ι → Nf Γ ι

--   data Ne : Cx ⋆ → ⋆ → Set where
--     _$_ : ∀ {Γ σ τ} → σ ∈ Γ → Sp Γ σ τ → Ne Γ τ

--   data Sp : Cx ⋆ → ⋆ → ⋆ → Set where
--     <> : ∀ {Γ σ} → Sp Γ σ σ
--     _,_ : ∀ {Γ σ τ ρ} → Nf Γ τ → Sp Γ σ ρ → Sp Γ (τ ▹ σ) ρ

-- mutual
--   wkNf : ∀ {Γ σ τ} → (x : σ ∈ Γ) → Nf (Γ -× x) τ → Nf Γ τ
--   wkNf x (λn t) = λn (wkNf (suc x) t)
--   wkNf x (ne (v $ sp)) = ne ((x ≠ v) $ wkSp x sp)

--   wkSp : ∀ {Γ σ τ ρ} → (x : σ ∈ Γ) → Sp (Γ -× x) τ ρ → Sp Γ τ ρ
--   wkSp x <> = <>
--   wkSp x (nf , sp) = wkNf x nf , wkSp x sp

-- appSp : ∀ {Γ τ σ ρ} → Sp Γ σ (ρ ▹ τ) → Nf Γ ρ → Sp Γ σ τ
-- appSp <> nf = nf , <>
-- appSp (x , sp) nf = x , appSp sp nf

-- -- I think this is (arguably) much easier
-- mutual
--   nvar : ∀ {σ Γ} → σ ∈ Γ → Nf Γ σ
--   nvar x = ne2nf (x $ <>)

--   ne2nf : ∀ {σ Γ} → Ne Γ σ → Nf Γ σ
--   ne2nf {ι} n = ne n
--   ne2nf {σ₁ ▹ σ₂} (x $ sp) = λn (ne2nf {σ₂} ((suc x) $ appSp (wkSp zero sp) (nvar zero)))


-- mutual
--   <_/_>_ : ∀ {Γ σ τ} → (x : σ ∈ Γ) → Nf (Γ -× x) σ → Nf Γ τ → Nf (Γ -× x) τ
--   < x / u > λn t = λn (< suc x / wkNf zero u > t)
--   < x / u > ne (y $ sp) with veq? x y
--   < x / u > ne (.x $ sp) | same = u $$ (< x / u >* sp)
--   < x / u > ne (.(x ≠ y) $ sp) | diff y = ne (y $ (< x / u >* sp))

--   <_/_>*_ : ∀ {Γ σ τ ρ} → (x : σ ∈ Γ) → Nf (Γ -× x) σ → Sp Γ τ ρ → Sp (Γ -× x) τ ρ
--   < x / u >* <> = <>
--   < x / u >* (n , sp) = < x / u > n , (< x / u >* sp)

--   _$$_ : ∀ {Γ τ} → Nf Γ τ → Sp Γ τ ι → Nf Γ ι
--   λn n $$ (u , sp) = (< zero / u > n) $$ sp
--   ne (x $ sp) $$ <> = ne (x $ sp)

-- normalize : ∀ {Γ σ} → Γ ⊢ σ → Nf Γ σ
-- normalize (var x) = nvar x
-- normalize (lam t) = λn (normalize t)
-- normalize (app t₁ t₂) with normalize t₁ | normalize t₂
-- normalize (app t₁ t₂) | λn q | r = < zero / r > q


try₁ : ε ⊨ (((ι ▹ ι) ▹ (ι ▹ ι)) ▹ (ι ▹ ι) ▹ (ι ▹ ι))
try₁ = normalize (lambda (λ x → x {{refl}}))

church₂ : ∀ {τ} → ε ⊢ (τ ▹ τ) ▹ τ ▹ τ
church₂ = lambda λ f → lambda λ x → app (f {{refl}}) (app (f {{refl}}) (x {{refl}}))

try₂ : ε ⊨ ((ι ▹ ι) ▹ (ι ▹ ι))
try₂ = normalize (app (app church₂ church₂) church₂)


data Stop (Γ : Cx ⋆) (τ : ⋆) : Set where
  var : τ ∈ Γ → Stop Γ τ
  _$_ : ∀ {σ} → Stop Γ (σ ▹ τ) → Γ ⊨ σ → Stop Γ τ

-- Ex 2.7
renSt : ∀ {Γ Δ τ} → Ren Γ Δ → Stop Γ τ → Stop Δ τ
renSt r (var x) = var (r x)
renSt r (u $ n) = renSt r u $ renNm r n

stopSp : ∀ {Γ τ} → Stop Γ τ → Γ ⊨* τ → Γ ⊨ ι
stopSp (var x) ss = x $ ss
stopSp (u $ n) ss = stopSp u (n , ss)

mutual
  Val : Cx ⋆ → ⋆ → Set
  Val Γ τ = Go Γ τ ⊹ Stop Γ τ

  Go : Cx ⋆ → ⋆ → Set
  Go Γ ι = Zero
  Go Γ (σ ▹ τ) = ∀ {Δ} → Ren Γ Δ → Val Δ σ → Val Δ τ

-- Ex 2.8
renVal : ∀ {Γ Δ} τ → Ren Γ Δ → Val Γ τ → Val Δ τ
renVal ι r (tt , ())
renVal (σ₁ ▹ σ₂) r (tt , go) = tt , (λ {Δ} r' v → go (r' ∘ r) v)
renVal τ r (ff , st) = ff , renSt r st

renVals : ∀ Θ {Γ Δ} → Ren Γ Δ → ⟦ Θ ⟧C (Val Γ) → ⟦ Θ ⟧C (Val Δ)
renVals ε r θ = <>
renVals (Θ ,, σ) r θ = renVals Θ r (fst θ) ,  renVal σ r (snd θ)

idEnv : ∀ Γ → ⟦ Γ ⟧C (Val Γ)
idEnv ε = <>
idEnv (Γ ,, σ) = renVals Γ suc (idEnv Γ) , ff , var zero

-- Ex 2.9
mutual
  apply : ∀ {Γ σ τ} → Val Γ (σ ▹ τ) → Val Γ σ → Val Γ τ
  apply (tt , go) s = go id s
  apply (ff , var x) s = ff , (var x $ quo _ s)
  apply (ff , (st $ x)) s = ff , ((st $ x) $ quo _ s)

  quo : ∀ {Γ} τ → Val Γ τ → Γ ⊨ τ
  quo ι (tt , ())
  quo (τ₁ ▹ τ₂) (tt , go) = lam (quo τ₂ (go suc (ff , var zero)))
  quo τ (ff , var x) = eta-long x _ (λ _ → id)
  quo τ (ff , (st $ x)) with quo _ (ff , st)
  quo τ (ff , (st $ x)) | lam r = < zero / x > r


-- Ex 2.10
eval : ∀ {Γ Δ τ} → Γ ⊢ τ → ⟦ Γ ⟧C (Val Δ) → Val Δ τ
eval (var zero) γ = snd γ
eval (var (suc x)) γ = eval (var x) (fst γ)
eval (lam t) γ = tt , (λ r v → eval t (renVals _ r γ , v))
eval (app a b) γ = apply (eval a γ) (eval b γ)

normByEval : ∀ {Γ τ} → Γ ⊢ τ → Γ ⊨ τ
normByEval {Γ} {τ} t = quo τ (eval t (idEnv Γ))

try₃ : ε ⊨ ((ι ▹ ι) ▹ (ι ▹ ι))
try₃ = normByEval (app (app church₂ church₂) church₂)
