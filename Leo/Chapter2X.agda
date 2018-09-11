{-# OPTIONS --without-K #-}

module Chapter2X where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

infix 4 _≡_

data _≡_ {a : Level} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

-- J and K

J : {ℓ ℓ' : Level} {A : Set ℓ} (a : A) (P : (b : A) → a ≡ b → Set ℓ') →
    P a refl → (b : A) → (p : a ≡ b) → P b p
J a P r .a refl = r

postulate -- eliminator form of K
  K' : {ℓ ℓ' : Level} {A : Set ℓ} (a : A) (P : a ≡ a → Set ℓ') →
       P refl → (p : a ≡ a) → P p

K : {ℓ : Level} {A : Set ℓ} (a : A) (p : a ≡ a) → (p ≡ refl)
K a p = K' a (λ q → q ≡ refl) refl p 

satisfiesK : {ℓ : Level} (A :  Set ℓ) → Set ℓ
satisfiesK A = (a : A) (p : a ≡ a) → p ≡ refl

isSet : {ℓ : Level} (A : Set ℓ) → Set ℓ
isSet A = (a b : A) (p q : a ≡ b) → p ≡ q

-- Theorem 7.2.1

set→k : {ℓ : Level} (A : Set ℓ) → isSet A → satisfiesK A
set→k A P a p = P a a p refl

-- via pattern matching
k→set : {ℓ : Level} (A : Set ℓ) → satisfiesK A → isSet A
k→set A P a .a p refl = P a p

-- using J
k→setJ : {ℓ : Level} (A : Set ℓ) → satisfiesK A → isSet A
k→setJ A P a b p q = J
                     a
                     (λ b e → J {!!} {!!} {!!} {!!} {!!})
                     {!!}
                     {!!}
                     {!!}
-- p (λ q s → p ≡ q) {!!} {!!} {!!}
