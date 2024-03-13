open import Agda.Builtin.Equality
open import Agda.Builtin.Nat renaming (Nat to ℕ) using (suc ; zero)
open import Agda.Primitive
open import Agda.Builtin.Sigma
 
data _⊎_ {ℓ κ}(A : Set ℓ)(B : Set κ) : Set (ℓ ⊔ κ) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
 
_×_ : ∀{ℓ κ} → Set ℓ → Set κ → Set (ℓ ⊔ κ)
A × B = Σ A λ _ → B
 
data ⊤ : Set where
  tt : ⊤
 
data ⊥ : Set where
 
sym : ∀{ℓ}{A : Set ℓ}{a b : A} → a ≡ b → b ≡ a
sym refl = refl
 
trans : ∀{ℓ}{A : Set ℓ}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl p = p
 
cong : ∀{ℓ κ}{A : Set ℓ}{B : Set κ}(f : A → B){a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl
 
-- Műveletek
_+_ : ℕ → ℕ → ℕ
zero + x = x
suc y + x = suc (y + x)
infixl 6 _+_
 
_-_ : ℕ → ℕ → ℕ
zero - x = zero
suc y - zero = suc y
suc y - suc x = y - x
 
_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + (x * y)
 
_! : ℕ → ℕ
zero ! = 1
suc x ! = suc x * (x !)
 
min : ℕ → ℕ → ℕ
min zero x = zero
min (suc y) zero = zero
min (suc y) (suc x) = suc (min y x)
 
max : ℕ → ℕ → ℕ
max zero x = x
max (suc y) zero = suc y
max (suc y) (suc x) = suc (max y x)
 
-- Bizonyítsd az alábbi egyenlőségeket!
-- A gyakfájlból lehet szükséges lesz pár már használt bizonyítás, azokat másold át ha szükséges.
 
sucr+ : (n m : ℕ) → n + suc m ≡ suc (n + m)
sucr+ zero m = refl
sucr+ (suc n) m = cong suc (sucr+ n m)

f₁ : (x y : ℕ) → suc x + suc y ≡ suc (suc (x + y))
f₁ x y = cong suc (sucr+ x y)
 
f₂ : (x y : ℕ) → y ≡ 0 → x + y ≡ x
f₂ zero zero x₁ = refl
f₂ (suc x) zero x₁ = cong suc (f₂ x zero x₁ )
 
f₃ : (x : ℕ) → min x 0 ≡ 0
f₃ zero = refl
f₃ (suc x) = refl
 
f₄ : (x : ℕ) → max x 0 ≡ x
f₄ zero = refl
f₄ (suc x) = cong suc refl
 
zerop- : (x : ℕ) → x - x ≡ 0
zerop- zero = refl
zerop- (suc x) = zerop- x
 
idr- : (x : ℕ) → x - 0 ≡ x
idr- zero = refl
idr- (suc x) = cong suc refl
 
mindec : (x y : ℕ) → (min x y ≡ x) ⊎ (min x y ≡ y)
mindec zero y = inl refl
mindec (suc x) zero = inl {!   !}
mindec (suc x) (suc y) = inl {!   !}
 
sub : (x y : ℕ) → min x y - max x y ≡ 0
sub zero y = refl
sub (suc x) zero = refl
sub (suc x) (suc y) = sub x y
 
sub₂ : (x y : ℕ) → min x y - x ≡ 0
sub₂ = {!!}
 
idempmax : (x : ℕ) → max x x ≡ x
idempmax = {!!}
 
minassoc : (x y z : ℕ) → min x (min y z) ≡ min (min x y) z
minassoc = {!!}
 
distrib+max : (x y z : ℕ) → x + max y z ≡ max (x + y) (x + z)
distrib+max = {!!}
 
move : (x y z : ℕ) → (3 + x) + y + z ≡ suc x + (suc y + suc z)
move = {!!}
 
*id : (x y : ℕ) → x * y ≡ 0 → (x ≡ 0) ⊎ (y ≡ 0)
*id = {!!}
 
+id : (x y : ℕ) → x + y ≡ 0 → (x ≡ 0) × (y ≡ 0)
+id = {!!}
 
-- hamis bizonyítások
-- ilyen +/--ba nem lesz
 
-- segédbizonyítás
suc≠0 : {x : ℕ} → suc x ≡ 0 → ⊥
suc≠0 ()
--    └── itt le tudtuk a bizonyítás nyelni a konstruktorok diszjunktsága miatt, ugye suc soha nem egyenlő zeroval
 
-- suc injektivitása
sucinj : {x y : ℕ} → suc x ≡ suc y → x ≡ y
sucinj refl = refl
 
up : (x y : ℕ) → x + suc y ≡ x → ⊥
up = {!!}
 
!≠0 : (x : ℕ) → x ! ≡ 0 → ⊥
!≠0 = {!!}
 
-- Konverzió
_=ℕ_ : ℕ → ℕ → Set
zero =ℕ zero = ⊤
zero =ℕ suc y = ⊥
suc x =ℕ zero = ⊥
suc x =ℕ suc y = x =ℕ y
 
l : (x y : ℕ) → x ≡ y → x =ℕ y
l = {!!}
 
r : (x y : ℕ) → x =ℕ y → x ≡ y
r = {!!}  