{-# OPTIONS --without-K #-}

module Soln1 where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; foldl; map; reverse; _++_; filter)
open import Data.String using (toList; String)
open import Data.Nat using (ℕ; _*_; _+_; _≟_)
open import Data.Nat.Show using (show)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Data.Maybe using (Maybe; just; nothing)
open import IO.Primitive using (IO; readFiniteFile; _>>=_; return)
open import Category.Applicative using (RawApplicative)
open import Data.List.Categorical using (applicative)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)
open import Level using (0ℓ)


next-digit : ℕ → ℕ → ℕ
next-digit a b = 10 * a + b


digit : Char → Maybe ℕ
digit '0' = just 0
digit '1' = just 1
digit '2' = just 2
digit '3' = just 3
digit '4' = just 4
digit '5' = just 5
digit '6' = just 6
digit '7' = just 7
digit '8' = just 8
digit '9' = just 9
digit _   = nothing


≟2020 : (x : ℕ) → Dec {0ℓ} (x ≡ 2020)
≟2020 x = x ≟ 2020


increment : List ℕ × Maybe ℕ → Maybe ℕ → List ℕ × Maybe ℕ
increment (ns , nothing) input = (ns , input)
increment (ns , just n) nothing = (n ∷ ns , nothing)
increment (ns , just n) (just n') = (ns , just (next-digit n n'))


parse : List Char → List ℕ
parse = reverse ∘ finalize ∘ foldl increment ([] , nothing) ∘ map digit
  where
    finalize : _
    finalize (ns , nothing) = ns
    finalize (ns , just n) = n ∷ ns


module _ where
  open import Codata.Musical.Costring
  import IO.Primitive

  putStrLn : String → IO ⊤
  putStrLn = IO.Primitive.putStrLn ∘ toCostring

  mapM' : ∀ {a b A B} → (A → IO {a} B) → List {b} A → IO ⊤
  mapM' f [] = return tt
  mapM' f (x ∷ xs) = f x >>= λ _ → mapM' f xs


main : IO ⊤
main = do
  inputs ← readFiniteFile "input1"

  let nums = parse (toList inputs)
      f1 x y = (x + y , x * y)
      out1 = f1 <$> nums ⊛ nums
      filt1 = filter (≟2020 ∘ proj₁) out1
      f2 x y z = (x + y + z , x * y * z)
      out2 = f2 <$> nums ⊛ nums ⊛ nums
      filt2 = filter (≟2020 ∘ proj₁) out2

  _ ← mapM' (putStrLn ∘ show ∘ proj₂) filt1
  mapM' (putStrLn ∘ show ∘ proj₂) filt2
  where
    open RawApplicative applicative