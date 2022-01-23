{-# OPTIONS --guardedness --allow-exec #-}


module Main where

open import Data.Product using (_×_; _,_; _,′_; ∃; ∃-syntax; proj₁; proj₂; uncurry′)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_; _<?_)
open import Data.Nat.Show using (show)
open import Data.Char using (Char; _≟_)
open import Data.String using (String; toList)
open import Data.List using (List; _∷_; []; head; length; lookup) renaming (map to lmap)
open import Data.List.Relation.Unary.All using (All)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no; Dec; does)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary using (IUniversal)
open import Function using (_$_; _∘_; case_of_)
open import Data.Bool using (Bool; true; false; _xor_)
open import Data.Sum using ([_,_])


record Policy : Set where
  constructor _P_
  field
    range : ℕ × ℕ
    letter : Char


count : Char → List Char → ℕ
count c [] = zero
count c (x ∷ xs) with c ≟ x
...| yes p = suc (count c xs)
...| no ¬p = count c xs


_⊣_ : Policy → List Char → Set
((min , max) P letter) ⊣ cs =
  let c = count letter cs
  in (min ≤ c) × (c ≤ max)


_⊣?_ : ∀ p cs → Dec (p ⊣ cs)
((min , max) P letter) ⊣? cs =
  let c = count letter cs
  in min ≤? c ×-dec c ≤? max

_⊣B_ : Policy → List Char → Bool
p ⊣B cs = does (p ⊣? cs)


_⊢B_ : Policy → List Char → Bool
((suc fst , suc snd) P letter) ⊢B cs =
  let l = length cs
  in  case ((fst <? l) ,′ (snd <? l) )
      of λ where
        (yes p1 , yes p2) →     does (letter ≟ lookup cs (fromℕ< p1))
                            xor does (letter ≟ lookup cs (fromℕ< p2))

        (yes p1 , no ¬p2) → does (letter ≟ lookup cs (fromℕ< p1))
        (no ¬p1 , yes p2) → does (letter ≟ lookup cs (fromℕ< p2))
        (no ¬p1 , no ¬p2) → false
  where open import Data.Fin using (fromℕ<)
((_ , _) P letter) ⊢B cs = false


open import Text.Parser hiding (_>>=_)

parsePolicy : ∀[ Parser Policy ]
parsePolicy =
  _P_
  <$> (decimalℕ <& box (char '-') <&> box (decimalℕ <& box spaces))
  <*> box (alpha <& box (char ':' &> box spaces))


parseLine : ∀[ Parser (Policy × List Char) ]
parseLine =
  parsePolicy <&> box (L⁺.toList <$> list⁺ (anyTokenBut '\n'))
  where import Data.List.NonEmpty as L⁺


parsePassword : ∀[ Parser Bool ]
parsePassword = uncurry′ _⊣B_ <$> parseLine


parsePassword' : ∀[ Parser Bool ]
parsePassword' = uncurry′ _⊢B_ <$> parseLine


parsePasswords : ∀[ Parser Bool ⇒ Parser ℕ ]
parsePasswords p =
  sumTrue ∘ L⁺.toList
  <$> list⁺ (p <& box (char '\n'))
  where
    import Data.List.NonEmpty as L⁺

    sumTrue : List Bool → ℕ
    sumTrue [] = zero
    sumTrue (true ∷ bs) = suc (sumTrue bs)
    sumTrue (false ∷ bs) = sumTrue bs


open import IO

main : Main
main = run $ do
  s ← readFiniteFile "input"
  [ (λ x → putStrLn "failed") , (λ n → putStrLn (show n)) ]
    (runParser (parsePasswords parsePassword') s)


_ : "1-3 a: abcde" ∈ parseLine
_ = (1 , 3) P 'a' , toList "abcde" !

_ : "1-3 a: abcde" ∈ parsePassword
_ = true !

_ : "1-3 a: abcde" ∈ parsePassword'
_ = true !
