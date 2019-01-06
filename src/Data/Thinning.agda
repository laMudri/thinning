module Data.Thinning where

  open import Data.Nat using (ℕ; zero; suc)

  data _≤_ : ℕ → ℕ → Set where
    oz :                    zero ≤ zero
    os : ∀ {m n} → m ≤ n → suc m ≤ suc n
    o′ : ∀ {m n} → m ≤ n →     m ≤ suc n
