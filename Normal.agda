module Normal where

open import Data.Nat
open import Data.Product hiding (zip; map; swap) renaming (proj₁ to fst; proj₂ to snd)
open import Function using (_∘_; id)
open import Agda.Builtin.Equality
open import Data.Empty

open import Vect

record Normal : Set₁ where
  constructor _/_
  field
    Shape : Set
    size : Shape → ℕ
  ⟦_⟧ : Set → Set
  ⟦_⟧ X = Σ[ x ∈ Shape ] (Vec X (size x))

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

instance
  fstHom : ∀ {X} → MonoidHom {⟦ ListN ⟧ X} {ℕ} fst
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

record ApplicativeOKP F {{AF : Applicative F}} : Set₁ where
  field
    lawId : ∀ {X} (x : F X) → (pure {{AF}} id ⊗ x) ≡ x
    lawCo : ∀ {R S T} (f : F (S → T)) (g : F (R → S)) (r : F R) →
            (pure {{AF}} (λ f g → f ∘ g) ⊗ f ⊗ g ⊗ r) ≡ (f ⊗ (g ⊗ r))
    lawHom : ∀ {S T} (f : S → T) (s : S) →
             (pure {{AF}} f ⊗ pure s) ≡ pure (f s)
    lawCom : ∀ {S T} (f : F (S → T)) (s : S) →
             (f ⊗ pure s) ≡ (pure {{AF}} (λ f → f s) ⊗ f)
  applicativeEndoFunctorOKP : EndoFunctorOKP F {{applicativeEndoFunctor}}
  applicativeEndoFunctorOKP = record
    { endoFunctorId = lawId
    ; endoFunctorCo = λ f g r →
            pure {{AF}} f ⊗ (pure {{AF}} g ⊗ r)
          ⟨ lawCo (pure f) (pure g) r ⟩≡
            pure {{AF}} (λ f g → f ∘ g) ⊗ pure f ⊗ pure g ⊗ r
         ≡⟨ cong (λ x → x ⊗ pure g ⊗ r) (lawHom (λ f g → f ∘ g ) f) ⟩
            pure {{AF}} (_∘_ f) ⊗ (pure g) ⊗ r
         ≡⟨ cong (λ x → x ⊗ r) (lawHom (_∘_ f) g) ⟩
            (pure {{AF}} (f ∘ g) ⊗ r □)
    }

-- Ex 1.20
vecApplicativeOKP : {n : ℕ} → ApplicativeOKP λ X → Vec X n
vecApplicativeOKP = record
  { lawId = vecId
  ; lawCo = vecCo
  ; lawHom = vecHom
  ; lawCom = vecCom
  } where
  vecId : ∀ {X n} (x : Vec X n) → vapp (vec id) x ≡ x
  vecId <> = refl
  vecId (x , xs) rewrite vecId xs = refl
  vecCo : ∀ {R S T n} → (f : Vec (S → T) n) → (g : Vec (R → S) n) → (r : Vec R n) →
          vapp (vapp (vapp (vec (λ f g → f ∘ g)) f) g) r ≡ vapp f (vapp g r)
  vecCo {n = zero} <> <> <> = refl
  vecCo {n = suc m} (f , fs) (g , gs) (r , rs) rewrite vecCo {n = m} fs gs rs  = refl
  vecHom : ∀ {S T n} → (f : S → T) (s : S) → vapp {n = n} (vec f) (vec s) ≡ vec (f s)
  vecHom {n = zero} f s = refl
  vecHom {n = suc m} f s rewrite vecHom {n = m} f s = refl
  vecCom : ∀ {S T n} → (f : Vec (S → T) n) (s : S) → vapp f (vec s) ≡ vapp (vec (λ f → f s)) f
  vecCom {n = zero} <> s = refl
  vecCom {n = suc m} (f , fs) s rewrite vecCom {n = m} fs s = refl


_→̇_ : ∀ (F G : Set → Set) → Set₁
F →̇ G = ∀ {X} → F X → G X

record AppHom {F} {{AF : Applicative F}} {G} {{AG : Applicative G}}
              (k : F →̇ G) : Set₁ where
  field
    respPure : ∀ {X} (x : X) → k (pure x) ≡ pure x
    resp⊗ : ∀ {S T} (f : F (S → T)) (s : F S) → k (f ⊗ s) ≡ (k f ⊗ k s)

monoidApplicativeHom :
  ∀ {X} {{MX : Monoid X}} {Y} {{MY : Monoid Y}}
  (f : X → Y) {{hf : MonoidHom f}} →
  AppHom {{monoidApplicative {{MX}}}} {{monoidApplicative {{MY}}}} f
monoidApplicativeHom f {{hf}} = record
  { respPure = λ x → MonoidHom.respε hf
  ; resp⊗ = MonoidHom.resp· hf
  }

-- Ex 1.21
homSum : ∀ {F G} {{AF : Applicative F}} {{AG : Applicative G}} →
         (f : F →̇ G) →
         Applicative λ X → F X ⊹ G X
homSum {F} {G} {{AF}} {{AG}} f = record
  { pure = λ x → tt , (pure x)
  ; _⊗_ = h
  } where
  h : ∀ {S T} → Σ Two (F (S → T) <?> G (S → T)) → Σ Two (F S <?> G S) → Σ Two (F T <?> G T)
  h (tt , fst) (tt , fs) = tt , (fst ⊗ fs)
  h (tt , fst) (ff , gs) = ff , (f fst ⊗ gs)
  h (ff , gst) (tt , fs) = ff , (gst ⊗ f fs)
  h (ff , gst) (ff , gs) = ff , (gst ⊗ gs)

-- Comment for the sake of compilation speed
-- homSumOKP : ∀ {F G} {{AF : Applicative F}} {{AG : Applicative G}} →
--             ApplicativeOKP F → ApplicativeOKP G →
--             (f : F →̇ G) → AppHom {{AF}} {{AG}} f →
--             ApplicativeOKP _ {{homSum {{AF}} {{AG}} f}}
-- homSumOKP {F} {G} {{AF}} {{AG}} FOK GOK f homf = record
--   { lawId = homSumId
--   ; lawCo = homSumCo
--   ; lawHom = homSumHom
--   ; lawCom = homSumCom
--   } where
--   homSumId : ∀ {X} (x : Σ Two (F X <?> G X)) →
--       (_⊗_ {{homSum f}} (pure {{homSum f}} id) x) ≡ x
--   homSumId (tt , fx) rewrite ApplicativeOKP.lawId FOK fx = refl
--   homSumId (ff , gx) =
--     cong (λ x → ff , x)
--          ((f (pure id)) ⊗ gx
--              ≡⟨ cong (λ x → _⊗_ x gx) (AppHom.respPure homf id) ⟩
--                 ApplicativeOKP.lawId GOK gx)
--   homSumCo : ∀ {R S T} → (fs : F (S → T) ⊹ G (S → T)) → (g : F (R → S) ⊹ G (R → S)) → (r : F R ⊹ G R) →
--              _⊗_ {{homSum f}} (_⊗_ {{homSum f}} (_⊗_ {{homSum f}} (pure {{homSum f}} (λ aa bb → aa ∘ bb)) fs) g) r
--              ≡ _⊗_ {{homSum f}} fs (_⊗_ {{homSum f}} g r)
--   homSumCo (tt , fst) (tt , frs) (tt , fr) = cong (λ x → (tt , x)) (ApplicativeOKP.lawCo FOK fst frs fr)
--   homSumCo (tt , fst) (tt , frs) (ff , gr) =
--     cong (λ x → (ff , x))
--     (f ((pure {{AF}} (λ f g → f ∘ g)) ⊗ fst ⊗ frs) ⊗ gr
--       ≡⟨ cong (λ x → x ⊗ gr) (AppHom.resp⊗ homf (pure {{AF}} (λ f g → f ∘ g) ⊗ fst) frs) ⟩
--     f (pure {{AF}} (λ f g → f ∘ g) ⊗ fst) ⊗ (f frs) ⊗ gr
--       ≡⟨ cong (λ x → x ⊗ (f frs) ⊗ gr) (AppHom.resp⊗ homf (pure (λ aa bb → aa ∘ bb)) fst) ⟩
--     f (pure (λ aa bb → aa ∘ bb)) ⊗ (f fst) ⊗ (f frs) ⊗ gr
--       ≡⟨ cong (λ x → x ⊗ (f fst) ⊗ (f frs) ⊗ gr) (AppHom.respPure homf (λ aa bb → aa ∘ bb)) ⟩
--     ApplicativeOKP.lawCo GOK (f fst) (f frs) gr)
--   homSumCo (tt , fst) (ff , grs) (tt , fr) =
--     cong (λ x → (ff , x)) (f (pure {{AF}} (λ f g → f ∘ g) ⊗ fst) ⊗ grs ⊗ (f fr)
--       ≡⟨ cong (λ x → x ⊗ grs ⊗ (f fr)) (AppHom.resp⊗ homf (pure (λ f g → f ∘ g)) fst) ⟩
--     f (pure (λ f g → f ∘ g)) ⊗ (f fst) ⊗ grs ⊗ (f fr)
--       ≡⟨ cong (λ x → x ⊗ (f fst) ⊗ grs ⊗ (f fr)) (AppHom.respPure homf (pure (λ f g → f ∘ g))) ⟩
--     ApplicativeOKP.lawCo GOK (f fst) grs (f fr))
--   homSumCo (tt , fst) (ff , grs) (ff , gr) =
--     cong (λ x → (ff , x)) (f (pure {{AF}} (λ f g → f ∘ g) ⊗ fst) ⊗ grs ⊗ gr
--       ≡⟨ cong (λ x → x ⊗ grs ⊗ gr) (AppHom.resp⊗ homf (pure (λ f g → f ∘ g)) fst) ⟩
--     f (pure (λ f g → f ∘ g)) ⊗ (f fst) ⊗ grs ⊗ gr
--       ≡⟨ cong (λ x → x ⊗ (f fst) ⊗ grs ⊗ gr) (AppHom.respPure homf (pure (λ f g → f ∘ g))) ⟩
--     ApplicativeOKP.lawCo GOK (f fst) grs gr)
--   homSumCo (ff , gst) (tt , frs) (tt , fr) =
--     cong (λ x → (ff , x)) (f (pure (λ f g → f ∘ g)) ⊗ gst ⊗ (f frs) ⊗ (f fr)
--       ≡⟨ cong (λ x → x ⊗ gst ⊗ (f frs) ⊗ (f fr)) (AppHom.respPure homf (λ f g → f ∘ g)) ⟩
--       (⟨⟩ (gst ⊗ (f (frs ⊗ fr))
--       ≡⟨ cong (λ x → gst ⊗ x) (AppHom.resp⊗ homf frs fr) ⟩
--       (⟨⟩ ApplicativeOKP.lawCo GOK gst (f frs) (f fr)))))
--   homSumCo (ff , gst) (tt , frs) (ff , gr) =
--     cong (λ x → (ff , x)) (f (pure (λ f g → f ∘ g)) ⊗ gst ⊗ (f frs) ⊗ gr
--       ≡⟨ cong (λ x → x ⊗ gst ⊗ (f frs) ⊗ gr) (AppHom.respPure homf (λ f g → f ∘ g)) ⟩
--     (ApplicativeOKP.lawCo GOK gst (f frs) gr))
--   homSumCo (ff , gst) (ff , grs) (tt , fr) =
--     cong (λ x → (ff , x)) (f (pure (λ f g → f ∘ g)) ⊗ gst ⊗ grs ⊗ (f fr)
--       ≡⟨ cong (λ x → x ⊗ gst ⊗ grs ⊗ (f fr)) (AppHom.respPure homf (λ f g → f ∘ g)) ⟩
--     (ApplicativeOKP.lawCo GOK gst grs (f fr)))
--   homSumCo (ff , gst) (ff , grs) (ff , gr) =
--     cong (λ x → (ff , x)) (f (pure (λ f g → f ∘ g)) ⊗ gst ⊗ grs ⊗ gr
--       ≡⟨ cong (λ x → x ⊗ gst ⊗ grs ⊗ gr) (AppHom.respPure homf (λ f g → f ∘ g)) ⟩
--     (ApplicativeOKP.lawCo GOK gst grs gr))
--   homSumHom : ∀ {S T} → (st : S → T) (s : S) →
--               (_⊗_ {{homSum f}} (pure {{homSum f}} st) (pure {{homSum f}} s)) ≡ (pure {{homSum f}} (st s))
--   homSumHom st s  = cong (λ x → (tt , x)) (ApplicativeOKP.lawHom FOK st s)
--   homSumCom : ∀ {S T} → (fg : F (S → T) ⊹ G (S → T)) (s : S) →
--               _⊗_ {{homSum f}} fg (pure {{homSum f}} s) ≡ _⊗_ {{homSum f}} (pure {{homSum f}} (λ f → f s)) fg
--   homSumCom (tt , fst) s = cong (λ x → (tt , x)) (ApplicativeOKP.lawCom FOK fst s)
--   homSumCom (ff , gst) s =
--     cong (λ x → (ff , x)) (gst ⊗ (f (pure s))
--       ≡⟨ (cong (λ x → gst ⊗ x) (AppHom.respPure homf s)) ⟩
--       (⟨⟩ (f (pure (λ fs → fs s)) ⊗ gst ≡⟨ cong (λ x → x ⊗ gst) (AppHom.respPure homf (λ fs → fs s)) ⟩
--       (⟨⟩ ApplicativeOKP.lawCom GOK gst s))))


record TraversableOKP F {{TF : Traversable F}} : Set₁ where
  field
    lawId : ∀ {X} (xs : F X) → traverse id xs ≡ xs
    lawCo : ∀ {G} {{AG : Applicative G}} {H} {{AH : Applicative H}}
              {R S T} (g : S → G T) (h : R → H S) (rs : F R) →
              let instance EH : EndoFunctor H; EH = applicativeEndoFunctor
              in map {H} (traverse g) (traverse h rs) ≡
                 traverse {{TF}} {{applicativeComp AH AG}} (map {H} g ∘ h) rs
    lawHom : ∀ {G} {{AG : Applicative G}} {H} {{AH : Applicative H}}
               (h : G →̇ H) {S T} (g : S → G T) → AppHom {G} h →
               (ss : F S) →
               traverse (h ∘ g) ss ≡ h (traverse g ss)

lengthContentsShape :
  ∀ {F} {{TF : Traversable F}} → TraversableOKP F →
  ∀ {X} (fx : F X) → fst (contextT fx) ≡ sizeT (shapeT fx)
lengthContentsShape tokF fx =
  fst (contextT fx)
    ⟨ TraversableOKP.lawHom tokF {{monoidApplicative}} {{monoidApplicative}}
        fst one (monoidApplicativeHom fst) fx ⟩≡
  sizeT fx ⟨ TraversableOKP.lawCo tokF {{monoidApplicative}} {{applicativeId}} (λ _ → 1) (λ _ → <>) fx ⟩≡ (sizeT (shapeT fx) □)

toNormal : ∀ {F} {{TF : Traversable F}} → TraversableOKP F →
           ∀ {X} → F X → ⟦ normalT F ⟧ X
toNormal tokF fx =
  (shapeT fx) , (subst (lengthContentsShape tokF fx) (Vec _) (snd (contextT fx)))


Batch : Set → Set → Set
Batch X Y = Σ[ n ∈ ℕ ] (Vec X n → Y)


chop : ∀ {m X} n → Vec X (n + m) → Vec X n × Vec X m
chop zero vx = <> , vx
chop (suc n) (x , vx) with chop n vx
chop (suc n) (x , vx) | a , b = (x , a) , b

instance
  applicativeBatch : ∀ {X} → Applicative (Batch X)
  applicativeBatch = record
    { pure = λ z → zero , (λ _ → z)
    ; _⊗_ = uncurry (λ m f → uncurry (λ n g → (n + m)
                    , (λ xx → let ss = chop n xx in f (snd ss) (g (fst ss)))))
    }

eno : ∀ {X} → Vec X 1 → X
eno (x , _) = x

help : ∀ {X F} {{TF : Traversable F}} → F One → Batch X (F X)
help {X} fx = traverse (λ _ → 1 , eno) fx

+suc : (a b : ℕ) → suc a + b ≡ a + suc b
+suc zero b = refl
+suc (suc a) b rewrite +suc a b = refl

+commu : (a b : ℕ) → a + b ≡ b + a
+commu zero b rewrite b +zero = refl
+commu (suc a) b rewrite +commu a b | +suc b a = refl

fstHom' : ∀ {X} → AppHom {{applicativeBatch {X}}} {{monoidApplicative}} fst
fstHom' = record { respPure = λ {X} x → refl ; resp⊗ = λ s f → +commu (fst f) (fst s) }


someConherence :
  ∀ {F} {{TF : Traversable F}} → TraversableOKP F →
  ∀ {X} → (fx : F One) → fst (help {X} fx) ≡ sizeT fx
someConherence tokF {X} fx =
  fst (help fx)
    ⟨ TraversableOKP.lawHom tokF {{applicativeBatch}} {{monoidApplicative}}
        fst (λ _ → 1 , eno) fstHom' fx ⟩≡
  TraversableOKP.lawCo tokF {{applicativeId}}{{monoidApplicative}}{S = X}
    (\ _ -> <>) (\ _ -> 1) fx

fromNormal : ∀ {F} {{TF : Traversable F}} → TraversableOKP F →
             ∀ {X} → ⟦ normalT F ⟧ X → F X
fromNormal tokF {X} (fx , vs) with help {X} fx | someConherence tokF {X} fx
fromNormal tokF (fx , vs) | _ , f | refl = f vs


data Tree (N : Normal) : Set where
  <_> : ⟦ N ⟧ (Tree N) → Tree N

NatT : Normal
NatT = Two / 0 <?> 1

zeroT : Tree NatT
zeroT = < (tt , <>) >

sucT : Tree NatT → Tree NatT
sucT n = < (ff , (n , <>)) >

NatInd : ∀ {l} (P : Tree NatT → Set l) →
           P zeroT →
           ((n : Tree NatT) → P n → P (sucT n)) →
           (n : Tree NatT) → P n
NatInd P z s < tt , <> > = z
NatInd P z s < ff , (x , <>) > = s x (NatInd P z s x)

All : ∀ {l X} (P : X → Set l) {n} → Vec X n → Set l
All P <> = One
All P (x , xs) = P x × All P xs

induction : ∀ (N : Normal) {l} (P : Tree N → Set l) →
              ((s : Shape N) (ts : Vec (Tree N) (size N s)) → All P ts → P < (s , ts) >) →
              (t : Tree N) → P t
induction N P p < s , ts > = p s ts (hyps ts) where
  hyps : ∀ {n} (ts : Vec (Tree N) n) → All P ts
  hyps <> = <>
  hyps (x , xs) = (induction N P p x) , (hyps xs)

Dec : Set → Set
Dec X = X ⊹ (X → ⊥)

mutual

  eqN? : (N : Normal) (sheq? : (s s' : Shape N) → Dec (s ≡ s')) →
        (t t' : Tree N) → (Dec (t ≡ t'))
  eqN? N sheq? < tsh , tvs > < t'sh , t'vs > with sheq? tsh t'sh
  eqN? N sheq? < tsh , tvs > < .tsh , t'vs > | tt , refl with eqs? N sheq? tvs t'vs
  eqN? N sheq? < tsh , tvs > < .tsh , .tvs > | tt , refl | tt , refl = tt , refl
  eqN? N sheq? < tsh , tvs > < .tsh , t'vs > | tt , refl | ff , no = ff , no ∘ inj
    where inj : ∀ {s} {tvs t'vs : Vec (Tree N) (size N s)} → < (s , tvs) > ≡ < (s , t'vs) > → tvs ≡ t'vs
          inj refl = refl
  eqN? N sheq? < tsh , tvs > < t'sh , t'vs > | ff , no = ff , no ∘ inj
    where inj : ∀ {s v} {tvs : Vec (Tree N) (size N s)} {t'vs : Vec (Tree N) (size N v)} → < (s , tvs) > ≡ < (v , t'vs) > → s ≡ v
          inj refl = refl

  eqs? : (N : Normal) (sheq? : (s s' : Shape N) → Dec (s ≡ s')) →
         {n : ℕ} (ts vs : Vec (Tree N) n) → Dec (ts ≡ vs)
  eqs? N sheq? {zero} <> <> = tt , refl
  eqs? N sheq? {suc n} (t , ts) (v , vs) with eqN? N sheq? t v | eqs? N sheq? ts vs
  eqs? N sheq? {suc n} (t , ts) (.t , .ts) | tt , refl | tt , refl = tt , refl
  eqs? N sheq? {suc n} (t , ts) (.t , vs) | tt , refl | ff , no = ff , (no ∘ inj)
    where inj : ∀ {n X} {v : X} {ts vs : Vec X n} → _≡_ {A = Vec X (suc n)} (v , ts) (v , vs) → ts ≡ vs
          inj refl = refl
  eqs? N sheq? {suc n} (t , ts) (v , vs) | ff , no | _ = ff , (no ∘ inj)
    where inj : ∀ {n X} {t v : X} {ts vs : Vec X n} → _≡_ {A = Vec X (suc n)} (t , ts) (v , vs) → t ≡ v
          inj refl = refl
