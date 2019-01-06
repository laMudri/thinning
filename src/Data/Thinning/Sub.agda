module Data.Thinning.Sub where

  open import Data.Empty
  open import Data.Nat using (ℕ; zero; suc; _+_)
  open import Data.Nat.Properties using (+-suc)
  open import Relation.Binary.PropositionalEquality

  open import Data.Thinning

  infix 4 _⊆_

  -- Sub-thinnings
  -- A thinning θ : m ≤ n describes a set of size m made up of elements from n.
  -- θ ⊆ φ iff φ keeps at least the elements from n that θ does.
  data _⊆_ : ∀ {m m′ n} → m ≤ n → m′ ≤ n → Set where
    ozz :                                                 oz ⊆ oz
    oss : ∀ {m m′ n} {θ : m ≤ n} {φ : m′ ≤ n} → θ ⊆ φ → os θ ⊆ os φ
    o′s : ∀ {m m′ n} {θ : m ≤ n} {φ : m′ ≤ n} → θ ⊆ φ → o′ θ ⊆ os φ
    o′′ : ∀ {m m′ n} {θ : m ≤ n} {φ : m′ ≤ n} → θ ⊆ φ → o′ θ ⊆ o′ φ

  oee : ∀ {m n} {θ : m ≤ n} → oe ⊆ θ
  oee {θ = oz} = ozz
  oee {θ = os θ} = o′s oee
  oee {θ = o′ θ} = o′′ oee

  oii : ∀ {m n} {θ : m ≤ n} → θ ⊆ θ
  oii {θ = oz} = ozz
  oii {θ = os θ} = oss oii
  oii {θ = o′ θ} = o′′ oii

  oei : ∀ {m n} {θ : m ≤ n} → θ ⊆ oi
  oei {θ = oz} = ozz
  oei {θ = os θ} = oss oei
  oei {θ = o′ θ} = o′s oei
