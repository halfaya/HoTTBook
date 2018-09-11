{-# OPTIONS --with-K #-}
--{-# OPTIONS --without-K #-}

module Chapter2K where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

infix 4 _≡_  _,_

data _≡_ {a : Level} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

data Prod (A B : Set) : Set where
  _×_ : A → B → Prod A B

-- J and K

J : {ℓ ℓ' : Level} {A : Set ℓ} (a : A) (P : (b : A) → a ≡ b → Set ℓ') →
    P a refl → (b : A) → (p : a ≡ b) → P b p
J a P r .a refl = r

-- fails if K is turned off
K : {ℓ ℓ' : Level} {A : Set ℓ} (a : A) (P : a ≡ a → Set ℓ') →
    P refl → (p : a ≡ a) → P p
K a P p refl = p

-- Remark 2.7.1

-- version with pattern matching

-- these fail even with K
--fails271 : (A : Set) → (P : A → Set) → (x : A) → (u v : P x) → (x , u) ≡ (x , v) → u ≡ v
--fails271 A P x u v p = {!!}
--fails271' : (A : Set) → (P : A → Set) → (x : A) → (u v : Σ A (λ x → P x)) → u ≡ v → proj₁ u ≡ proj₁ v → proj₂ u ≡ proj₂ v
--fails271' A P x u v p = {!!}

-- fails if K is turned off
ok271 : (A : Set) → (P : A → Set) → (x : A) → (u v : P x) → (x × u) ≡ (x × v) → u ≡ v
ok271 A P x u .u refl = refl

-- also fails if K is turned off
ok271' : (A B : Set) → (x : A) → (u v : B) → (x × u) ≡ (x × v) → u ≡ v
ok271' A P x u .u refl = refl

-- version with J and K

--ok271K : (A B : Set) → (x : A) → (u v : B) → (x × u) ≡ (x × v) → u ≡ v
--ok271K A P x u v p = {!!}
