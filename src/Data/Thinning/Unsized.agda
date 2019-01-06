module Data.Thinning.Unsized where

  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Product

  open import Data.Thinning
  open import Data.Thinning.Sub

  infix 4 _⊆u_

  ThSet : ℕ → Set
  ThSet n = ∃ λ m → m ≤ n

  uz : ThSet zero
  uz = zero , oz

  us : ∀ {n} → ThSet n → ThSet (suc n)
  us (m , θ) = (suc m , os θ)

  u′ : ∀ {n} → ThSet n → ThSet (suc n)
  u′ (m , θ) = (m , o′ θ)

  _⊆u_ : ∀ {n} (X Y : ThSet n) → Set
  (_ , θ) ⊆u (_ , φ) = θ ⊆ φ
