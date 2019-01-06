module Data.Thinning.Complement where

  open import Data.Empty
  open import Data.Nat using (ℕ; zero; suc; _+_)
  open import Data.Product as Σ
  open import Function using (id)
  open import Relation.Binary.PropositionalEquality

  open import Data.Thinning
  open import Data.Thinning.Unsized

  infixl 8 _ᶜ

  -- Set complement
  _ᶜ : ∀ {n} → ThSet n → ThSet n
  (.zero , oz) ᶜ = uz
  (suc m , os θ) ᶜ = u′ ((m , θ) ᶜ)
  (m , o′ θ) ᶜ = us ((m , θ) ᶜ)

  oe-ᶜ : ∀ n → (0 , oe) ᶜ ≡ (n , oi)
  oe-ᶜ zero = refl
  oe-ᶜ (suc n) = cong us (oe-ᶜ n)

  oi-ᶜ : ∀ n → (n , oi) ᶜ ≡ (0 , oe)
  oi-ᶜ zero = refl
  oi-ᶜ (suc n) = cong u′ (oi-ᶜ n)

  ᶜ-ᶜ : ∀ {n} (θ : ThSet n) → (θ ᶜ) ᶜ ≡ θ
  ᶜ-ᶜ (.zero , oz) = refl
  ᶜ-ᶜ (suc m , os θ) = cong us (ᶜ-ᶜ (m , θ))
  ᶜ-ᶜ (m , o′ θ) = cong u′ (ᶜ-ᶜ (m , θ))

  -- n - m, as justified by the fact that m is smaller
  -- This is the number of elements that the thinning dropped.
  diff : ∀ {m n} → m ≤ n → ℕ
  diff θ = proj₁ ((_ , θ) ᶜ)

  -- All that was dropped is kept, and vice-versa.
  complement : ∀ {m n} (θ : m ≤ n) → diff θ ≤ n
  complement θ = proj₂ ((_ , θ) ᶜ)
