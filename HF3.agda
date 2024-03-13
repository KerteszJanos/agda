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
id↔ = (λ x → x) , (λ x → x)
 
--                          A           B
id↔const : {A B : Set} → (A → A) ↔ (A → B → A)
id↔const = (λ x y z → x y) , λ x y → y
--id↔const = (λ x y z → y) ,                          λ x y → y
--         (A -> A) -> (A -> B -> A)                (A -> B -> A) -> (A -> A)
--            x         y    z                            x           y

asd : {A B : Set} -> (A ⊎ B) -> (B ⊎ A)
asd (inr x) = inl x
asd (inl x) = inr x
--asd = λ {(inl x) → inr x
--       ; (inr x) → inl x}

comm⊎ : {A B : Set} → (A ⊎ B) ↔ (B ⊎ A)
fst comm⊎ (inr x) = inl x
fst comm⊎ (inl x) = inr x
snd comm⊎ (inr x) = inl x
snd comm⊎ (inl x) = inr x
--comm⊎ = (λ {(inl x) → inr x
--          ; (inr x) → inl x}) , λ {(inl x) → inr x
--                                 ; (inr x) → inl x}

comm× : {A B : Set} → (A × B) ↔ (A × B)
comm× = (λ { x → x}) , (λ x → x)
--fst comm× = λ {x .fst → fst x
--             ; x .snd → snd x}
--snd comm× = λ {x .fst → fst x
--             ; x .snd → snd x}
 
-- hosszabb              A         B
comm↔ : {A B : Set} → (A ↔ B) ↔ (B ↔ A)
fst comm↔ = λ {x .fst → snd x
             ; x .snd → fst x}
snd comm↔ = λ {(x , y) → (y , x)}
--comm↔ = (λ {(x , y) → (y , x)}) ,               λ {(x , y) → (y , x)}
--      ((A ↔ B)    →    (B ↔ A))
--   (A → B , B → A) (B → A , A → B)

r₁ : {A B C : Set} → (A × (B ⊎ C)) ↔ ((C ⊎ B) × A)
fst r₁ = λ {(x , inl y) → inr y , x
          ; (x , inr y) → inl y , x}
snd r₁ = λ {(x , y) .fst → y
          ; (inl x , y) .snd → inr x
          ; (inr x , y) .snd → inl x}
 
distrib : {A B C : Set} → (A × (B ⊎ C)) ↔ ((A × B) ⊎ (A × C))
--(A × (B ⊎ C)) → ((A × B) ⊎ (A × C))
fst distrib = λ {(x , inl y) → inl (x , y)
               ; (x , inr y) → inr (x , y)}
--((A × B) ⊎ (A × C)) → (A × (B ⊎ C))
snd distrib = λ {(inl x) → (fst x) , (inl (snd x))
               ; (inr (x , y)) → x , inr y}

-- nehezebb
plus0 : {A B : Set} → (A ↔ B) ↔ ((A ⊎ ⊥) ↔ (B ⊎ ⊥))
--    (A ↔ B)    →          ((A ⊎ ⊥) ↔ (B ⊎ ⊥))
--(A → B , B → A) ((A ⊎ ⊥) → (B ⊎ ⊥) , (B ⊎ ⊥) → (A ⊎ ⊥))   
fst plus0 = λ {(x , y) → (λ {(inl x₁) → inl (x x₁)}) , λ {(inl x₁) → inl (y x₁)}}

--          ((A ⊎ ⊥) ↔ (B ⊎ ⊥))           →     (A ↔ B)
--((A ⊎ ⊥) → (B ⊎ ⊥) , (B ⊎ ⊥) → (A ⊎ ⊥))  (A → B , B → A)
snd plus0 = λ {(x , y) → (λ a → case (x (inl a)) (λ b → b) (λ b → exfalso b)) , 
                          λ b → case ((y (inl b))) (λ a → a) (λ b → exfalso b)}

-- nehezebb
times1 : {A B : Set} → (A ↔ B) ↔ ((A × ⊤) ↔ (B × ⊤))
times1 = {!!}
 
trans↔ : {A B C : Set} → (A ↔ B) → (B ↔ C) → (A ↔ C)
trans↔ = {!!}
 
curry : {A B C : Set} → (A × B → C) ↔ (A → B → C)
curry = {!!}
 
⊥ext : {A : Set} → (A → ⊥) → A ↔ ⊥
⊥ext = {!!}
 
classic : ((Bool → ⊥) → ⊥) ↔ Bool
classic = {!!}
 
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
--(A ⊎ A) -> (Bool × A)
fst a+a=2a = λ {(inl x) → true , x
              ; (inr x) → false , x}
--(Bool × A) -> (A ⊎ A)
snd a+a=2a = λ {(false , y) → inr y
              ; (true , y) → inl y}
 
bija+a=2a : {A : Set}{t : A}{b : Bool} → fst a+a=2a (snd a+a=2a (b , t)) ≡ (b , t)
bija+a=2a {b = true} = refl
bija+a=2a {b = false} = refl
 
a*[b+1]=a*b+a : {A B : Set} → (A × (B ⊎ ⊤)) ↔ ((A × B) ⊎ A)
--(A × (B ⊎ ⊤)) → ((A × B) ⊎ A)
fst a*[b+1]=a*b+a = λ {(x , inl y) → inl (x , y)
                     ; (x , inr y) → inr x}
--((A × B) ⊎ A) → (A × (B ⊎ ⊤))
snd a*[b+1]=a*b+a = λ {(inl (x , y)) → x , inl y
                     ; (inr x) → x , inr tt}
 
bija*[b+1]=a*b+a : {A B : Set}{a : A}{b : B ⊎ ⊤} → snd a*[b+1]=a*b+a (fst a*[b+1]=a*b+a (a , b)) ≡ (a , b)
bija*[b+1]=a*b+a {b = inl x} = refl
bija*[b+1]=a*b+a {b = inr tt} = refl
     