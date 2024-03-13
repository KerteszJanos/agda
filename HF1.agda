module HF1 where
 
open import Agda.Builtin.Nat renaming (Nat to ℕ)
 
-- Billentyű kombinációk!
 
-- C-c C-SPC - Hole-ba beszúrás
-- C-c C-r   - Refine, holeba írt kifejezés beillesztése
-- C-c C-l   - Fájl betöltése
-- C-c C-n   - Kifejezés kiértékelése
-- ű         - Unicode input (Emacson \)
 
-- Unicode inputok
-- bN = ℕ
-- to = →
-- Gl = λ
 
fib : ℕ → ℕ
fib zero = 0
fib (suc zero) = 1
fib (suc (suc n)) = fib (suc n) + fib n

-- Definiálj egy függvényt ami megszoroz egy számot 17-el!
-- Definiáld lambdával is!
 
mul17 : ℕ → ℕ
mul17 a = a * 17
 
mul17' : ℕ → ℕ
mul17' = λ a → a * 17
 
-- Vegyük az alábbi függvényt. Mennyi az értéke, ha 187-ra kiértékeljük? (Használj C-c C-n-t) 36356 
func : ℕ → ℕ
func = λ n → n * n + 3 * n + n * 4 + 78
 
-- Definiálj egy kifejezést aminek a típusa ℕ és az értéke megegyezik a func függvény értékével 1211-ben!
func2 : ℕ → ℕ
func2 = λ a → a + 35145
-- Definiálj egy függvényt ami egy ℕ → ℕ függvényt kap paraméterül és azt a függvényt alkalmazza a 13-ra!
 
applyto13 : (ℕ → ℕ) → ℕ
applyto13 a = a 13
 
-- Definiálj egy függvényt ami egy ℕ → ℕ → ℕ függvényt kap paraméterül és azt a függvényt az 5-re és 3-ra alkalmazza!
 
applyto5and3 : (ℕ → ℕ → ℕ) → ℕ
applyto5and3 = λ a → a 5 3
 
-- Definiálj egy függvényt ami egy ℕ → ℕ → ℕ függvényt és egy természetes számot kap paraméterül, majd eredményül visszaadja az első paraméterül kapott függvényt alkalmazva a második paraméterül kapott
-- számra és az 5-re!
-- pl.: funky (_+_) 4 ≡ 9, mert 4 + 5 = 9 vagy funky (λ x y → y) 13 ≡ 5
 
funky : (ℕ → ℕ → ℕ) → ℕ → ℕ
funky = λ a b → a b 5
 
-- Definiáld az f g függvényeket, úgy hogy f mul17 ≠ g mul17
f g : (ℕ → ℕ) → ℕ
f = λ a → (a 1)
g = λ a → (a 1) + 1
 
-- Definiáld h i j függvényeket, úgy hogy h 1 = i 1, i 2 ≠ j 2 és j 3 = h 4 = h 0
h i j : ℕ → ℕ
h a = 1
i a = a
j a = 1
 
-- Nehezebb feladatok
 
-- Vegyük az alábbi függvényt
 
superfunky : ((ℕ → ℕ) → ℕ) → ℕ
superfunky f = f (λ x → x + 1)
 
-- Mi lenne az alábbi kifejezések eredménye? (C-c C-n előtt próbáld meg kitalálni!)
-- superfunky applyto13             = 14
-- superfunky (λ f → f (f 5))       = 7
-- superfunky f //λ a → (a 1)       = 2
-- superfunky g //λ a → (a 1) + 1   = 3
 
-- Definiálj egy függvényt ami egy számot és egy ℕ → ℕ függvényt vár paraméterül. A kapott függvényt alkalmazza 5-ször a kapott számra, majd adjon hozzá 3-at.
-- A függvény neve legyen alkalmazo.
-- Mennyi alkalmazo 13 (λ x → x + 1) értéke? = 21
alkalmazo : ℕ → (ℕ → ℕ) → ℕ
alkalmazo n f = f(f(f(f(f(n))))) + 3
-- Definiáljunk egy függvényt, ami az alábbi polinómot számolja ki egy adott X értékben: x²+3x+15
 
--pow : ℕ → ℕ → ℕ
--pow 

polynomial : ℕ → ℕ
polynomial = λ x → x * x + 3 * x + 15
 
-- Definiáljuk a k l függvényeket, úgy hogy k (λ x y → x + y) = l (λ x y → x * y) és k (λ x y → x) ≠ l (λ x y → y + 1)
 
k l : (ℕ → ℕ → ℕ) → ℕ
k a = a 1 1
l a = a 1 2
 
-- Van e működési különbség az alábbi függvények között?
{-
 
f : ℕ → ℕ
f = λ x → x + 3
 
és
 
f : ℕ → ℕ
f x = 3 + x

Aennyiben az összeadás sorrendje nem számít működési különbségnek, nincs.
-}
 
-- Mi a baj az alábbi kódrészletekkel? Javítsd ki őket, ha van hiba!
 
--Nem vette át a paramétert
f1 : ℕ → ℕ
f1 a = 3
 
-- mul17 ℕ-t vár paraméterül.
f2 : ℕ
f2 = (mul17 (mul17 1))
 
--Nincs mert fordul :D, mondjuk azt nem tudom miért xd
f3 : ℕ → (ℕ → ℕ)
f3 x y = x + y

--simple 
f4 : (ℕ → ℕ) → (ℕ → ℕ)
f4 x = x

 
f5 : ((ℕ → ℕ) → ℕ) → ℕ
f5 f = f (_+ 1)
--f5 f = f (λ x → x + 1)
