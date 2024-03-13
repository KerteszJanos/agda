open import Agda.Builtin.Unit
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Primitive
 
-- DEFINÍCIÓK
 
record _×_ {ℓ κ}(A : Set ℓ)(B : Set κ) : Set (ℓ ⊔ κ) where
  constructor _,_
  field
    fst : A
    snd : B
 
open _×_ public
 
data _⊎_ {ℓ κ}(A : Set ℓ)(B : Set κ) : Set (ℓ ⊔ κ) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
 
case : ∀{ℓ κ μ}{A : Set ℓ}{B : Set κ}{C : Set μ} → A ⊎ B → (A → C) → (B → C) → C
case (inl a) a→c b→c = a→c a
case (inr b) a→c b→c = b→c b
 
data ⊥ : Set where
 
exfalso : ∀{ℓ}{A : Set ℓ} → ⊥ → A
exfalso ()
 
_↔_ : ∀{ℓ κ} → Set ℓ → Set κ → Set (ℓ ⊔ κ)
A ↔ B = (A → B) × (B → A)
 
-- Új billentyűkombinációk
-- (Ha hole-ba fv kell) C-c C-c ENTER = felveszi a paramétereket
-- (Ha hole-ba × kell) C-c C-c ENTER = comintailleszt
 
id↔ : {A : Set} → A ↔ A
id↔ = (λ x → x) , λ x → x
 
id↔const : {A B : Set} → (A → A) ↔ (A → B → A)
fst id↔const = λ x y z → y
snd id↔const = λ x y → y
 
comm⊎ : {A B : Set} → (A ⊎ B) ↔ (B ⊎ A)
fst comm⊎ = λ {(inl x) → inr x
             ; (inr x) → inl x}
snd comm⊎ = λ {(inl x) → inr x
             ; (inr x) → inl x}
 
comm× : {A B : Set} → (A × B) ↔ (A × B)
fst comm× = λ {(a , b) → a , b}
snd comm× = λ x → x
 
-- hosszabb
comm↔ : {A B : Set} → (A ↔ B) ↔ (B ↔ A)
fst comm↔ = λ {(ab , ba) → (λ b → ba b) , λ a → ab a}
snd comm↔ = λ {(ba , ab) → (λ x → ab x) , (λ x → ba x)}
 
r₁ : {A B C : Set} → (A × (B ⊎ C)) ↔ ((C ⊎ B) × A)
fst r₁ = λ {(a , inl x) → inr x , a
          ; (a , inr x) → inl x , a}
snd r₁ = λ {(inl x , a) → a , inr x
          ; (inr x , a) → a , inl x}
 
distrib : {A B C : Set} → (A × (B ⊎ C)) ↔ ((A × B) ⊎ (A × C))
fst distrib = λ {(a , inl x) → inl (a , x)
               ; (a , inr x) → inr (a , x)}
snd distrib = λ {(inl x) → (fst x) , (inl (snd x))
               ; (inr x) → (fst x) , (inr (snd x))}
 
-- nehezebb
plus0 : {A B : Set} → (A ↔ B) ↔ ((A ⊎ ⊥) ↔ (B ⊎ ⊥))
fst plus0 = λ {(ab , ba) → (λ {(inl x) → inl (ab x)}) , λ {(inl x) → inl (ba x)}}
snd plus0 = λ {(abbb , bbab) → (λ {a → case (abbb (inl a)) (λ x → x) λ x → exfalso x}) , {!   !}}
 
-- nehezebb
times1 : {A B : Set} → (A ↔ B) ↔ ((A × ⊤) ↔ (B × ⊤))
fst times1 = λ {x → (λ {(a , t) → (fst x) a , t}) , λ {(b , t) → snd x b , tt}}
snd times1 = {!   !}
 
trans↔ : {A B C : Set} → (A ↔ B) → (B ↔ C) → (A ↔ C)
trans↔ = λ {(ab , ba) (bc , cb) → (λ x → bc (ab x)) , (λ x → ba (cb x))}
 
curry : {A B C : Set} → (A × B → C) ↔ (A → B → C)
fst curry = λ a,bc a b → a,bc (a , b)
snd curry = λ x y → x (fst y) (snd y)
 
⊥ext : {A : Set} → (A → ⊥) → A ↔ ⊥
⊥ext = λ z → z , (λ ())
 
classic : ((Bool → ⊥) → ⊥) ↔ Bool
classic = (λ x → false) , (λ x x₁ → x₁ x)
 
-- TESZTELT BIJEKCIÓK
-- Ezek olyan bijekciók, amiket meg lehet típushelyesen, de rosszul írni.
-- Ezért automata tesztek vannak hozzájuk csatolva
 
-- Példa:
 
^↔ : {A : Set} → (A × A) ↔ (Bool → A)
fst ^↔ x false = fst x
fst ^↔ x true = snd x
snd ^↔ f = f false , f true
 
-- Itt a bizonyítás azt mondja,
-- hogy minden t : A × A kifejezés esetén ha először az első részét az előző függvénynek alkalmazzuk, majd a másodikat, visszakapjuk az eredeti értéket.
-- Tehát f(g(x)) = x (azaz a bijekció egy definíciója)
bij^↔ : {A : Set}{t : A × A} → snd ^↔ (fst ^↔ t) ≡ t
bij^↔ = refl
 
-- Ha olyan definíciót adnánk meg, ami ezeket nem tejesíti az agda reklamálna
-- Itt egy hibás eset, ha kikommenteled hibát ír
 
{-
^↔' : {A : Set} → (A × A) ↔ (Bool → A)
fst ^↔' x _ = fst x
snd ^↔' f = f false , f false
 
bij^↔' : {A : Set}{t : A × A} → snd ^↔' (fst ^↔' t) ≡ t
bij^↔' = refl
-}
 
a+a=2a : {A : Set} → (A ⊎ A) ↔ (Bool × A)
a+a=2a = {!!}
 
bija+a=2a : {A : Set}{t : A}{b : Bool} → fst a+a=2a (snd a+a=2a (b , t)) ≡ (b , t)
bija+a=2a {b = true} = refl
bija+a=2a {b = false} = refl
 
a*[b+1]=a*b+a : {A B : Set} → (A × (B ⊎ ⊤)) ↔ ((A × B) ⊎ A)
a*[b+1]=a*b+a = {!!}
 
bija*[b+1]=a*b+a : {A B : Set}{a : A}{b : B ⊎ ⊤} → snd a*[b+1]=a*b+a (fst a*[b+1]=a*b+a (a , b)) ≡ (a , b)
bija*[b+1]=a*b+a {b = inl x} = refl
bija*[b+1]=a*b+a {b = inr tt} = refl 