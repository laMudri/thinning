module Data.Thinning.Union where

  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Product

  open import Data.Thinning
  open import Data.Thinning.Sub
  open import Data.Thinning.Unsized

  infixr 6 _∪_

  -- Union of sets
  -- Elements are kept iff they are kept by either of the two thinnings.
  _∪_ : ∀ {n} (X Y : ThSet n) → ThSet n
  (.zero ,   oz) ∪        Y       = Y
  (    l , o′ θ) ∪ (    m , o′ φ) = u′ ((l , θ) ∪ (m , φ))
  (    l , o′ θ) ∪ (suc m , os φ) = us ((l , θ) ∪ (m , φ))
  (suc l , os θ) ∪ (    m , o′ φ) = us ((l , θ) ∪ (m , φ))
  (suc l , os θ) ∪ (suc m , os φ) = us ((l , θ) ∪ (m , φ))

  inl : ∀ {n} {X Y : ThSet n} → X ⊆u X ∪ Y
  inl {X = .zero ,   oz} = oee
  inl {X =     l , o′ θ} {    m , o′ φ} = o′′ inl
  inl {X =     l , o′ θ} {suc m , os φ} = o′s inl
  inl {X = suc l , os θ} {    m , o′ φ} = oss inl
  inl {X = suc l , os θ} {suc m , os φ} = oss inl

  inr : ∀ {n} {X Y : ThSet n} → Y ⊆u X ∪ Y
  inr {X = .zero ,   oz} = oii
  inr {X =     l , o′ θ} {    m , o′ φ} = o′′ (inr {X = l , θ})
  inr {X =     l , o′ θ} {suc m , os φ} = oss (inr {X = l , θ})
  inr {X = suc l , os θ} {    m , o′ φ} = o′s (inr {X = l , θ})
  inr {X = suc l , os θ} {suc m , os φ} = oss (inr {X = l , θ})

  [_,_] : ∀ {n} {X Y Z : ThSet n} → X ⊆u Z → Y ⊆u Z → (X ∪ Y) ⊆u Z
  [_,_] {X = _ ,   oz}                 XZ       YZ  = YZ
  [_,_] {X = _ , o′ θ} {_ , o′ φ} (o′′ XZ) (o′′ YZ) = o′′ [ XZ , YZ ]
  [_,_] {X = _ , o′ θ} {_ , o′ φ} (o′s XZ) (o′s YZ) = o′s [ XZ , YZ ]
  [_,_] {X = _ , o′ θ} {_ , os φ} (o′s XZ) (oss YZ) = oss [ XZ , YZ ]
  [_,_] {X = _ , os θ} {_ , o′ φ} (oss XZ) (o′s YZ) = oss [ XZ , YZ ]
  [_,_] {X = _ , os θ} {_ , os φ} (oss XZ) (oss YZ) = oss [ XZ , YZ ]
