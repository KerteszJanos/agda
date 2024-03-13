open import Agda.Primitive
open import Agda.Builtin.Nat using (suc; zero; _+_) renaming (Nat to ℕ)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
 
record Σ {ℓ κ}(A : Set ℓ)(P : A → Set κ) : Set (ℓ ⊔ κ) where
  constructor _,_
  field
    fst : A
    snd : P fst
 
open Σ public
{-# BUILTIN SIGMA Σ #-}
 
{-
 
Ugyanaz, csak komintailleszteni nem lehet
 
data Σ {ℓ κ}(A : Set ℓ)(P : A → Set κ) : Set (ℓ ⊔ κ) where
  _,_ : (a : A) → P a → Σ A P
 
-}
 
_×_ : ∀{ℓ κ} → Set ℓ → Set κ → Set (ℓ ⊔ κ)
A × B = Σ A λ _ → B
 
_↔_ : ∀{ℓ κ} → Set ℓ → Set κ → Set (ℓ ⊔ κ)
A ↔ B = (A → B) × (B → A)
 
data ⊥ : Set where
 
exfalso : ∀{ℓ}{A : Set ℓ} → ⊥ → A
exfalso ()
 
record ⊤ : Set where
  instance constructor tt
 
open ⊤ public
 
¬_ : ∀{ℓ} → Set ℓ → Set ℓ
¬ A = A → ⊥
 
infixr 5 ¬_
 
data _⊎_ {ℓ κ}(A : Set ℓ)(B : Set κ) : Set (ℓ ⊔ κ) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
 
data Vec {ℓ}(A : Set ℓ) : ℕ → Set ℓ where
  [] : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
 
infixr 5 _∷_
 
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)
 
{- LOGIKAI JELÖLÉS TÁBLAZAT
+---------------+---------------+---------------+
| Név           | Logika        | Agda          |
+---------------+---------------+---------------+
| Negáció       | ¬ A           | A → ⊥         |
+---------------+---------------+---------------+
| Implikáció    | A ⊃ B         | A → B         |
+---------------+---------------+---------------+
| Diszjunkció   | A ∨ B         | A ⊎ B         |
+---------------+---------------+---------------+
| Konjunkció    | A ∧ B         | A × B         |
+---------------+---------------+---------------+
-}
 
-- Definiáljuk az alábbi függőtípusos bijekciókat!
vec2a : {A : Set} → Vec A 1 ↔ A
fst vec2a (x ∷ xs) = x
snd vec2a x = x ∷ []
 
vec2a2 : {A : Set} → Vec A 2 ↔ (A × A)
fst vec2a2 (x ∷ xx ∷ xs) = x , xx
snd vec2a2 (f , s) = f ∷ s ∷ [] --(A × A) -> Vec A 2
 
t₁ : {A : Set}{a b : A} → fst vec2a2 (snd vec2a2 (a , b)) ≡ (a , b)
t₁ = refl
 
fin↔⊥ : Fin 0 ↔ ⊥
fst fin↔⊥ ()
snd fin↔⊥ ()
 
fin↔⊤ : Fin 1 ↔ ⊤
fst fin↔⊤ x = tt
snd fin↔⊤ x = zero
 
fin↔Bool : Fin 2 ↔ Bool
fst fin↔Bool zero = false
fst fin↔Bool (suc x) = true
snd fin↔Bool false = zero
snd fin↔Bool true = suc zero
 
t₂ : {b : Bool} → fst fin↔Bool (snd fin↔Bool b) ≡ b
t₂ {false} = refl
t₂ {true} = refl
  
Σlassoc : {A B : Set}{P : A → Set} → (Σ (A × B) λ t → P (fst t)) ↔ (Σ A λ a → B × (P a))
fst Σlassoc ((ff , fs) , s) = ff , (fs , s)
snd Σlassoc (f , s) = (f , fst s) , (snd s)
 
ΠΣ⊤ : {P : ⊤ → Set} → ((t : ⊤) → P t) ↔ Σ ⊤ P
fst ΠΣ⊤ x = tt , (x tt)
snd ΠΣ⊤ (tt , s) tt = s
 

Σdistrib : {A B : Set}{P : A ⊎ B → Set} → (Σ (A ⊎ B) P) ↔ ((Σ A λ a → P (inl a)) ⊎ (Σ B λ b → P (inr b)))
fst Σdistrib (inl a , p) = inl (a , p)
fst Σdistrib (inr b , p) = inr (b , p)
snd Σdistrib (inl x) = inl (fst x) , snd x
snd Σdistrib (inr x) = inr (fst x) , snd x
 
skipcurry : {A B D : Set}{C : A → Set} → ((a : A) → B → C a → D) ↔ ((Σ (A × B) λ t → C (fst t)) → D)
fst skipcurry x ((ff , fs) , s) = x ff fs s
snd skipcurry x A B Ca = x ((A , B) , Ca)
 
-- NEHEZEBB BIKEJCIÓK
-- Ezeknél típust is át kell adni egy pár helyen paraméterként
 
ctrΣ : (A : Set)(B : A → Set) → Σ A B ↔ ((C : Set) → ((a : A) → B a → C) → C)
fst (ctrΣ A B) ΣAB C a→Ba->C = a→Ba->C (fst ΣAB) (snd ΣAB)
snd (ctrΣ set a→set) C→a→Ba→C = C→a→Ba→C set (λ a _ → a) , C→a→Ba→C (a→set (C→a→Ba→C set (λ a _ → a))) {!   !}
 
ctr⊎ : (A B C : Set) → (A ⊎ B) ↔ ((C : Set) → (A → C) → (B → C) → C)
fst (ctr⊎ A B C) A⊎B set A→C B→C = A→C {! !}
snd (ctr⊎ A B C) = {!   !}
 
-- LOGIKA
-- Példa időutazásos levezetés
-- 1. Felvesszük a paramétert. Mivel ¬ A ≝ A → ⊥ ezért ⊥-ba képzünk és a bemeneti paraméter típusa ¬ (A ⊎ (¬ A))
wklem₁ : {A : Set} → ¬ ¬ (A ⊎ (¬ A))
wklem₁ ¬[a∨¬a] = ¬[a∨¬a] (inr (λ x → ¬[a∨¬a] (inl x)))
--               ^ C-c C-, szerint ⊥
 
-- 2. Ha ⊥-ot kell megadnunk akkor az "idő végén" vagyunk, meg kell néznünk mivel tudunk visszamenni az időben
-- Megkeressük mik képeznek ⊥-ba
-- ∙ Ha csak 1 függvényünk van ami abba képez képesek vagyunk azt használni (most ez a szitu)
-- ∙ Ha több opció van meg kell nézni melyik függvény milyen információt tud bevezetni nekünk
--   Egy függvény akkor vezet be információ, ha függvény a paramétere
--   Pl.: ((A → B) → ⊥)-ban A számít bevezethető információnak
--        ((A ⊎ (A → ⊥)) → ⊥)-ban A számít bevezethető információnak
--               ^ ez az A
--        (((A → C) × B) → ⊥)-ban A számít bevezethető információnak, de csak ha B-t meg tudjuk adni
--           ^ ez az A
--   Amikor függvényt választunk, csak olyan függvényt válasszunk ami (logikai szempontból) új információt vezet be
-- ∙ Ha már minden lehetség információt bevezettünk így, akkor lehet olyan függvényeket keresni amik ⊥-ba térnek vissza és NEM ⊥-ba
--   visszatérő függvényt várnak paraméterül.
--   Pl.: A → ⊥
--        (B → A) → ⊥
--        (A × B) → ⊥
--   Meg kell nézni ezek közül melyiket tudjuk előállítani és akkor ott be tudjuk fejezni a függvény írását
-- Itt most az első esetet tudjuk alkalmazni
 
wklem₂ : {A : Set} → ¬ ¬ (A ⊎ (¬ A))
wklem₂ ¬[a∨¬a] = ¬[a∨¬a] (inr (λ x → ¬[a∨¬a] (inl x)))
--                        ^ C-c C-, szerint A ⊎ ¬ A
-- A két oldal közül A-t (per pillanat) csak exfalso-val tudnánk előállítani ami megint az idő végére (⊥) vezetne
-- A bal oldalba nekünk A → ⊥ típusú kifejezést kéne írni, ami szintén az idő végére visz, de vezed be nekünk A-t információként
 
wklem₃ : {A : Set} → ¬ ¬ (A ⊎ (¬ A))
wklem₃ ¬[a∨¬a] = ¬[a∨¬a] (inr (λ a → ¬[a∨¬a] (inl a)))
--                                    ^ C-c C-, szerint ⊥
-- Megint az idő végén vagyunk
-- Általunk ismert információ:
-- ¬[a∨¬a] : ¬ (A ⊎ (¬ A))
-- a : A
-- Még mindig csak 1 kifejezésünk van ami ⊥-ba képez, de itt már a 3. pontban tudunk gondolkodni. A ¬[a∨¬a] kifejezés tartalmaz egy NEM
-- ⊥-ba képző fv-t paraméterül
-- ¬[a∨¬a] : ¬ (A ⊎ (¬ A))
--              ^ ő itt
-- A típusú kifejezésünk pedig már van, tehát annak a segítségével meg tudunk állni
 
wklem₄ : {A : Set} → ¬ ¬ (A ⊎ (¬ A))
wklem₄ ¬[a∨¬a] = ¬[a∨¬a] (inr (λ a → ¬[a∨¬a] (inl a)))
--                       │                           │
--                       └───────────────────────────┘ itt egyébként látható, hogy az A ⊎ (¬ A) bizonyításához
--                                                     külső információra szükség volt
 
-- FELADATOK
 
left-proj : {A B : Set} → A × B → A
left-proj (f , s) = f
 
right-proj : {A B : Set} → A × B → B
right-proj = snd
 
modus-ponens : {A B : Set} → (A → B) × A → B
modus-ponens (f , s) = f s
 
transpose : {A B : Set} → (A → B) → ¬ B → ¬ A
transpose A→B ¬B A = ¬B (A→B A)

 
∨-syll : {A B : Set} → A ⊎ B → ¬ B → A
∨-syll (inl x) ¬B = x
∨-syll (inr x) ¬B = exfalso (¬B x)
 
lem→pow : {A : Set} → A ⊎ (¬ A) → ¬ ¬ A → A
lem→pow (inl x) ¬¬A = x
lem→pow (inr x) ¬¬A = exfalso (¬¬A x)
 
contra : {A B : Set} → A × (¬ A) → B
contra (A , ¬A) = exfalso (¬A A)
 
biproj : {A B C : Set} → (A → C) × (B → C) → A ⊎ B → C
biproj (A→C , B→C) (inl x) = A→C x
biproj (A→C , B→C) (inr x) = B→C x
 
decurry : {A B C : Set} → A × B → (A → B → C) → C
decurry (A , B) A→B→C = A→B→C A B
 
dm-contra : {A B : Set} → ¬ (A ⊎ (¬ A)) → B
dm-contra x = exfalso (x (inr λ a → x (inl a)))
 
mat-impl : {A B : Set} → (¬ ¬ (A → B)) ↔ (¬ ¬ ((¬ A) ⊎ B))
mat-impl = {!!}
 
wk-⊤ : {A : Set} → ¬ ¬ ((¬ A → A) → A)
wk-⊤ = {!!}
 
rewrite₁ : {A B : Set} → (¬ (A × B)) ↔ (A → ¬ B)
rewrite₁ = {!!}    