module Data.Thinning.Complement where

  open import Data.Empty
  open import Data.Nat using (ℕ; zero; suc; _+_)
  open import Data.Product as Σ
  open import Relation.Binary.PropositionalEquality

  open import Data.Thinning

  -- n - m, as justified by the fact that m is smaller
  -- This is the number of elements that the thinning dropped.
  diff : ∀ {m n} → m ≤ n → ℕ
  diff oz = 0
  diff (os θ) = diff θ
  diff (o′ θ) = suc (diff θ)

  -- All that was dropped is kept, and vice-versa.
  _ᶜ : ∀ {m n} (θ : m ≤ n) → diff θ ≤ n
  oz ᶜ = oz
  os θ ᶜ = o′ (θ ᶜ)
  o′ θ ᶜ = os (θ ᶜ)

  -- Lemmas

  oe-ᶜ : ∀ n → ∃ λ (q : diff (oe {n}) ≡ n) → subst (_≤ n) q (oe ᶜ) ≡ oi
  oe-ᶜ zero = refl , refl
  oe-ᶜ (suc n) with diff (oe {n}) | oe {n} ᶜ | oe-ᶜ n
  ... | .n | .oi | refl , refl = refl , refl

  oi-ᶜ : ∀ n → ∃ λ (q : diff (oi {n}) ≡ 0) → subst (_≤ n) q (oi ᶜ) ≡ oe
  oi-ᶜ zero = refl , refl
  oi-ᶜ (suc n) with diff (oi {n}) | oi {n} ᶜ | oi-ᶜ n
  ... | .0 | .oe | refl , refl = refl , refl
