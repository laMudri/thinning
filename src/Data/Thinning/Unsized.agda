module Data.Thinning.Unsized where

  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Product

  open import Data.Thinning
  open import Data.Thinning.Sub

  ThSet : ℕ → Set
  ThSet n = ∃ λ m → m ≤ n

  uz : ThSet zero
  uz = zero , oz

  us : ∀ {n} → ThSet n → ThSet (suc n)
  us (m , θ) = (suc m , os θ)

  u′ : ∀ {n} → ThSet n → ThSet (suc n)
  u′ (m , θ) = (m , o′ θ)

  _⊆′_ : ∀ {n} (X Y : ThSet n) → Set
  (_ , θ) ⊆′ (_ , φ) = θ ⊆ φ
