{-# OPTIONS --without-K #-}

module Cubical where

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

-- J, etc

J : {ℓ ℓ' : Level} {A : Set ℓ} (a : A) (P : (b : A) → a ≡ b → Set ℓ') →
    P a refl → (b : A) → (p : a ≡ b) → P b p
J a P r .a refl = r

transport : {ℓ : Level} {A B : Set ℓ} → (A ≡ B) → A → B
transport refl a = a

Singleton : (ℓ : Level) → (A : Set ℓ) → (a : A) → Set ℓ
Singleton ℓ A a = Σ A (λ x → (x ≡ a))

singletonsContractable : {ℓ : Level} {A : Set ℓ} {a : A} (s : Singleton ℓ A a) → s ≡ (a , refl)
singletonsContractable (x , refl) = refl

-- J = contractability of singletons + transport

transport' : {ℓ : Level} {A B : Set ℓ} → (A ≡ B) → A → B
transport' = {!!}

singletonsContractable' : {ℓ : Level} {A : Set ℓ} {a : A} (s : Singleton ℓ A a) → s ≡ (a , refl)
singletonsContractable' = {!!}
