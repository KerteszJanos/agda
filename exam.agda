-- BEGIN FIX
{-# OPTIONS --guardedness #-}

open import Agda.Primitive

open import Agda.Builtin.Nat
  renaming (Nat to ℕ)
  public
open import Agda.Primitive
Type = Set
open import Agda.Builtin.Equality
  public
open import Agda.Builtin.Bool
  public
open import Agda.Builtin.Sigma
  public

infixr 5 _∷_
infixr 2 _×_
infixr 1 _⊎_
infix 0 _↔_

if_then_else_ : ∀{i}{A : Set i}(t : Bool)(u v : A) → A
if true  then u else v = u
if false then u else v = v

-- Product types
_×_ : ∀{ℓ κ} → Set ℓ → Set κ → Set (ℓ ⊔ κ)
A × B = Σ A λ _ → B

-- Sum types
data _⊎_ {i}{j}(A : Set i)(B : Set j) : Set (i ⊔ j) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

case : ∀ {i j k}{A : Set i}{B : Set j}{C : Set k}
         (t : A ⊎ B)(u : A → C)(v : B → C) → C
case (inl t) u v = u t
case (inr t) u v = v t

-- Empty type
data ⊥ : Set where

exfalso : ∀{i}{A : Set i} → ⊥ → A
exfalso ()

Dec : ∀{i} → Set i → Set i
Dec X = X ⊎ (X → ⊥)

-- Unit type
record ⊤ : Set where
  constructor tt
open ⊤ public

_↔_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A ↔ B = (A → B) × (B → A)

¬_ : ∀{i} → Set i → Set i
¬ A = A → ⊥

infix 4 _≢_
_≢_ : ∀{i}{A : Set i} → A → A → Set i
a ≢ b = ¬ (a ≡ b)

infixr 10 _!
_! : ℕ → ℕ
0 ! = 1
(suc x) ! = (suc x) * x !

-- infinite stream
record Stream {ℓ}(A : Set ℓ) : Set ℓ where
  coinductive
  constructor mkStream
  field
    head : A
    tail : Stream A

open Stream public

-- fixed-length vectors
data Vec {ℓ}(A : Set ℓ) : ℕ → Set ℓ where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

infixr 5 _++_
_++_ : ∀{i}{n m : ℕ}{A : Set i} → Vec A n → Vec A m → Vec A (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

-- maybe type
data Maybe {ℓ}(A : Set ℓ) : Set ℓ where
  nothing : Maybe A
  just : A → Maybe A

-- Finite natural numbers
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc  : {n : ℕ} → Fin n → Fin (suc n)

-- coinductive natural numbers (nat ∪ {∞})
record ℕ∞ : Set where
  coinductive
  constructor mkCoNat
  field
    pred∞ : Maybe ℕ∞

open ℕ∞ public

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀{i j}{A : Set i}{B : Set j}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : ∀{i j}{A : Set i}(P : A → Set j){x y : A} → x ≡ y → P x → P y
subst P refl p = p

ass+ : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
ass+ zero    b c = refl
ass+ (suc a) b c = cong suc (ass+ a b c)

idr+ : (a : ℕ) → a + 0 ≡ a
idr+ zero    = refl
idr+ (suc a) = cong suc (idr+ a)

+suc : (a b : ℕ) → suc a + b ≡ a + suc b
+suc zero    b = refl
+suc (suc a) b = cong suc (+suc a b)

comm+ : (a b : ℕ) → a + b ≡ b + a
comm+ zero b = sym (idr+ b)
comm+ (suc a) b = trans (cong suc (comm+ a b)) (+suc b a)

infix 4 _≤_
_≤_ : ℕ → ℕ → Set
x ≤ y = Σ ℕ λ m → m + x ≡ y

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

infix  3 _∎
infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∎ : ∀{i}{A : Set i}(a : A) → a ≡ a
a ∎ = refl

takeStream : ∀{ℓ}{A : Set ℓ}(n : ℕ) → Stream A → Vec A n
takeStream zero x = []
takeStream (suc n) x = (head x) ∷ (takeStream n (tail x))

dropStream : ∀{ℓ}{A : Set ℓ}(n : ℕ) → Stream A → Stream A
dropStream zero x = x
dropStream (suc n) x = dropStream n (tail x)

mapStream : ∀{ℓ κ}{A : Set ℓ}{B : Set κ} → (A → B) → Stream A → Stream B
head (mapStream f sa) = f (head sa)
tail (mapStream f sa) = mapStream f (tail sa)

iterate : ∀{ℓ}{A : Set ℓ} → (A → A) → A → Stream A
head (iterate f a) = a
tail (iterate f a) = iterate f (f a)

0∞ 1∞ 2∞ 3∞ 4∞ 5∞ 6∞ 7∞ 8∞ 9∞ 10∞ 11∞ 12∞ 13∞ 14∞ ∞ : ℕ∞
pred∞  0∞ = nothing
pred∞  1∞ = just 0∞
pred∞  2∞ = just 1∞
pred∞  3∞ = just 2∞
pred∞  4∞ = just 3∞
pred∞  5∞ = just 4∞
pred∞  6∞ = just 5∞
pred∞  7∞ = just 6∞
pred∞  8∞ = just 7∞
pred∞  9∞ = just 8∞
pred∞ 10∞ = just 9∞
pred∞ 11∞ = just 10∞
pred∞ 12∞ = just 11∞
pred∞ 13∞ = just 12∞
pred∞ 14∞ = just 13∞
pred∞ ∞   = just ∞

pred∞' : Maybe ℕ∞ → Maybe ℕ∞
pred∞' nothing = nothing
pred∞' (just n∞) = pred∞ n∞

helper : ℕ → ℕ → Bool
helper zero zero = true
helper zero (suc c) = false
helper (suc n) zero = false
helper (suc n) (suc c)= helper n c
-- BEGIN FIX
is1000 : ℕ → Bool
-- END FIX
is1000 x = helper x 1000


-- BEGIN FIX
test-is1000-1 : is1000 1000 ≡ true
test-is1000-1 = refl
test-is1000-2 : is1000 999 ≡ false
test-is1000-2 = refl
test-is1000-3 : is1000 1001 ≡ false
test-is1000-3 = refl
test-is1000-4 : is1000 0 ≡ false
test-is1000-4 = refl
-- END FIX

-- BEGIN FIX
coc∨ : (A B : Set) → A ⊎ B ↔ ((C : Set) → (A → C) → (B → C) → C)
-- END FIX
fst (coc∨ A B) (inl x) C ac bc = ac x
fst (coc∨ A B) (inr x) C ac bc = bc x
snd (coc∨ A B) x = x (A ⊎ B) (λ a → inl a) (λ b → inr b)

-- BEGIN FIX
logeq3 : (A : Set)(P : A → Set)(Q : A → Set) → (Σ A λ a → P a ⊎ Q a) ↔ Σ A P ⊎ Σ A Q
-- END FIX
fst (logeq3 A P Q) = λ x → case (snd x) (λ asd → inl (fst x , asd)) {!   !}
--fst (logeq3 A P Q) = λ x → inl ( fst x , case (snd x) (λ z → z) (λ Qfstx → {!   !}))
snd (logeq3 A P Q) (inl x) = {!   !}
snd (logeq3 A P Q) (inr x) = {!   !}


-- BEGIN FIX
¬¬lem : (X : Set) → (¬ (¬ X ⊎ X)) → ⊥
-- END FIX
¬¬lem X f = f (inl (λ x → f (inr x)))
--                    |
--      időutazással nyert információ


-- BEGIN FIX
lemma5 : (n : ℕ) → 3 ≡ n → ¬ (n ≡ 2)
-- END FIX
lemma5 .2 () refl
--lemma5 .3 refl ()

-- BEGIN FIX
≤n+ : (x y n : ℕ) → x ≤ y → x ≤ n + y
-- END FIX
≤n+ x .(zero + x) n (zero , refl) = n , refl
≤n+ x .(suc f + x) n (suc f , refl) = n + (suc f) , trans (ass+ n (suc f) x) refl

-- BEGIN FIX
decχ : (n k : ℕ) → Dec ((P : ℕ → Set) → P n → P k)
-- END FIX
decχ = {!   !}

--decχ n k = inl λ P x → exfalso {!  !}

--decχ n k = inr λ x → x (λ n → ⊥) {! P k  !}
--          |
--         no

¬*≤ : ¬ ((x y a : ℕ) → (a * x) ≤ (a * y) ↔ x ≤ y)
¬*≤ = {!   !}
--¬*≤ x with x 2 1 0
--... | f , s with f (snd f)
--... | pr = {!  !}

-- BEGIN FIX
→∀ : Dec ((A : Set)(P : A → Set)(Q : A → Set) → ((∀ x → P x) → (∀ x → Q x)) → ∀ x → P x → Q x)
-- END FIX
→∀ = {!   !}
--→∀ = inl (λ A P Q x a pa → x (λ a → {!   !}) a)
--→∀ = inr (λ x → x ⊤ (λ t → ⊥) (λ t → {!   !}) {!   !} {!   !} {!   !})

-- BEGIN FIX
-- Fűzzünk egy Stream elé véges számú elemet az adott sorrendben.
_++ₛ_ : ∀{i}{n : ℕ}{A : Set i} → Vec A n → Stream A → Stream A
-- END FIX
head ([] ++ₛ sA) = (head sA)
head ((x ∷ vA) ++ₛ sA) = x
tail ([] ++ₛ sA) = tail sA
tail ((x ∷ vA) ++ₛ sA) = vA ++ₛ sA

-- BEGIN FIX
++-test-1 : takeStream 6 ((1 ∷ 2 ∷ 3 ∷ []) ++ₛ iterate (λ x → x) 4) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 4 ∷ 4 ∷ []
++-test-1 = refl
++-test-2 : takeStream 7 ((false ∷ true ∷ false ∷ []) ++ₛ iterate (λ x → if x then false else true) false) ≡ false ∷ true ∷ false ∷ false ∷ true ∷ false ∷ true ∷ []
++-test-2 = refl
++-test-3 : {A : Set}{ys : Stream A} → (takeStream 5 ([] ++ₛ ys) ≡ takeStream 5 ys)
++-test-3 = refl
++-test-4 : takeStream 8 ((90 ∷ 100 ∷ 4 ∷ 20 ∷ 40 ∷ []) ++ₛ iterate suc 0) ≡ 90 ∷ 100 ∷ 4 ∷ 20 ∷ 40 ∷ 0 ∷ 1 ∷ 2 ∷ []
++-test-4 = refl
-- END FIX
 
 