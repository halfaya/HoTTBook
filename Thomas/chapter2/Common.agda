module Common where

open import Agda.Primitive
  using (Level; _⊔_)

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data Σ {a} {b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  _,_ : (a : A) → B a → Σ A B

prod : ∀ {α} {β} → (A : Set α) → (B : Set β) → Set (α ⊔ β)
prod {α} {β} A B = Σ {α} {β} A (\a → B)

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN EQUALITY _≡_  #-}

ind : ∀ {α β} → (A : Set α) → (C : (x y : A) → x ≡ y → Set β) →
        ((x : A) → C x x refl) → (x y : A) → (p : x ≡ y) → C x y p
ind A C c x .x refl = c x

based_ind : ∀ {α β} → (A : Set α) → (a : A) → (C : (x : A) → a ≡ x → Set β) →
                 C a refl → (x : A) → (p : a ≡ x) → C x p
based_ind A a C c .a refl = c
