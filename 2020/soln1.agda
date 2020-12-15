{-# OPTIONS --without-K #-}

module Soln1 where

open import Data.Char using (Char)
open import Data.String using (toList; String)
open import Data.Nat using (ℕ; _*_; _+_; _≟_; suc; zero)
open import Data.Nat.Show using (show)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; _$_)
open import Data.Maybe using (Maybe; just; nothing)
open import IO.Primitive using (IO; readFiniteFile; _>>=_; return)
open import Category.Applicative using (RawApplicative)
open import Data.List.Categorical using (applicative)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)
open import Level using (0ℓ)

private
  variable
    A B : Set

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


module _ where
  open import Data.List using (List; []; _∷_; foldl; map; reverse; _++_; filter; length)

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


  open import Codata.Musical.Costring
  import IO.Primitive

  putStrLn : String → IO ⊤
  putStrLn = IO.Primitive.putStrLn ∘ toCostring

  mapM' : (A → IO {0ℓ} B) → List {0ℓ} A → IO ⊤
  mapM' f [] = return tt
  mapM' f (x ∷ xs) = f x >>= λ _ → mapM' f xs



module _ where
  open import Data.Vec using (Vec; []; _∷_; [_]; map; _++_)

  module Hidden where
    f : ℕ → ℕ → ℕ
    f zero _ = suc zero
    f (suc r) zero = zero
    f (suc r) (suc n) = f r n + f (suc r) n


  open Hidden

  combinations : {n : ℕ} → (r : ℕ) → Vec A n → Vec (Vec A r) (f r n)
  combinations zero _ = [ [] ]
  combinations (suc r) [] = []
  combinations (suc r) (x ∷ xs) = map (x ∷_) (combinations r xs) ++ combinations (suc r) xs



main : IO ⊤
main = do
  inputs ← readFiniteFile "input1"

  let nums = vfromList $ parse (toList inputs)

      out2 = map f2 (combinations 2 nums)
      filt2 = filter (≟2020 ∘ proj₁) (vtoList out2)

      out3 = map f3 (combinations 3 nums)
      filt3 = filter (≟2020 ∘ proj₁) (vtoList out3)

  mapM' (putStrLn ∘ show ∘ proj₂) filt2
  mapM' (putStrLn ∘ show ∘ proj₂) filt3

  where
      open import Data.List using (filter)
      open import Data.Vec using (Vec; []; _∷_; [_]; map; _++_) renaming (toList to vtoList; fromList to vfromList)

      f2 : Vec ℕ 2 → ℕ × ℕ
      f2 (x ∷ y ∷ []) = (x + y , x * y)

      f3 : Vec ℕ 3 → ℕ × ℕ
      f3 (x ∷ y ∷ z ∷ []) = (x + y + z , x * y * z)

      _>>_ : IO A → IO B → IO B
      _>>_ a b = a >>= λ _ → b