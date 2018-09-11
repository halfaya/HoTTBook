{-# OPTIONS --without-K #-}

module Chapter2 where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

infix 4 _≡_
data _≡_ {α : Level} {A : Set α} (x : A) : A → Set α where
  refl : x ≡ x

data Σ {α β : Level} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
  _,_ : (a : A) → B a → Σ A B

{-# BUILTIN EQUALITY _≡_ #-}

ind : {α β : Level} → (A : Set α) →
     (C : (x y : A) → x ≡ y → Set β) →
     ((x : A) → C x x refl) →
     (x y : A) → (p : x ≡ y) → C x y p
ind A C c x .x refl = c x

ind' : {α β : Level} → (A : Set α) →
       (a : A) → 
       (C : (x : A) → a ≡ x → Set β) →
       C a refl →
       (x : A) → (p : a ≡ x) → C x p
ind' A a C c .a refl = c

----

data Eq {α : Level} (A : Set α) : A → A → Set α where
  refl : (x : A) → Eq A x x

indEq : {α β : Level} → (A : Set α) →
     (C : (x y : A) → Eq A x y → Set β) →
     ((x : A) → C x x (refl x)) →
     (x y : A) → (p : Eq A x y) → C x y p
indEq A C c x .x (refl .x) = c x

-- Lemma 2.1.1

sym : {α : Level} (A : Set α) → (a b : A) → a ≡ b → b ≡ a
sym A a b p = ind A (λ x y _ → y ≡ x) (λ _ → refl) a b p

_⁻¹ : {α : Level} {A : Set α} → {a b : A} → a ≡ b → b ≡ a
_⁻¹ {α} {A} {a} {b} p = sym A a b p

-- induction on p and then q
trans₁ : {α : Level} (A : Set α) → (a b c : A) → a ≡ b → b ≡ c → a ≡ c
--trans₁ A _ _ _ refl refl = refl
trans₁ A a b c p q = (ind A
                          (λ x y _ → (z : A) → y ≡ z → x ≡ z)
                          (λ x z r → ind A (λ x z _ → x ≡ z) (λ _ → refl) x z r)
                          a b p) c q

_◾_ : {α : Level} {A : Set α} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
_◾_ {α} {A} {a} {b} {c} p q = trans₁ A a b c p q

-- Lemma 2.1.4(i)

p≡p◾refl : {α : Level} {A : Set α} → {x y : A} → (p : x ≡ y) → p ≡ p ◾ refl {α} {A} {y}
p≡p◾refl {α} {A} {x} {y} p = ind A
                                 (λ a b q → q ≡ q ◾ refl {α} {A} {b})
                                 (λ c → refl {α} {_≡_ {α} {A} c c} {refl {α} {A} {c}})
                                 x y p


p≡refl◾p : {α : Level} {A : Set α} → {x y : A} → (p : x ≡ y) → p ≡ refl {α} {A} {x} ◾ p
p≡refl◾p {α} {A} {x} {y} p = ind A
                             (λ a b q → q ≡ refl {α} {A} {a} ◾ q)
                             (λ c → refl {α} {_≡_ {α} {A} c c} {refl {α} {A} {c}})
                             x y p

-- Lemma 2.1.4(ii)

p⁻¹◾p≡refl : {α : Level} {A : Set α} → {x y : A} → (p : x ≡ y) → (p ⁻¹) ◾ p ≡ refl {α} {A} {y}
p⁻¹◾p≡refl {α} {A} {x} {y} p = ind A
                               (λ a b q → (q ⁻¹) ◾ q ≡ refl {α} {A} {b})
                               (λ c → refl {α} {c ≡ c} {refl {α} {A} {c}})
                               x y p

p◾p⁻¹≡refl : {α : Level} {A : Set α} → {x y : A} → (p : x ≡ y) → p ◾ (p ⁻¹) ≡ refl {α} {A} {x}
p◾p⁻¹≡refl {α} {A} {x} {y} p = ind A
                               (λ a b q → q ◾ (q ⁻¹) ≡ refl {α} {A} {a})
                               (λ c → refl {α} {c ≡ c} {refl {α} {A} {c}})
                               x y p

-- Lemma 2.1.4(iii)

p⁻¹⁻¹≡p : {α : Level} {A : Set α} → {x y : A} → (p : x ≡ y) → (p ⁻¹) ⁻¹ ≡ p
p⁻¹⁻¹≡p {α} {A} {x} {y} p = ind A
                            (λ _ _ p → (p ⁻¹) ⁻¹ ≡ p)
                            (λ _ → refl)
                            x y p

-- Lemma 2.1.4(iv)

p◾[q◾r]≡[p◾q]◾r : {α : Level} {A : Set α} → {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → p ◾ (q ◾ r) ≡ (p ◾ q) ◾ r
p◾[q◾r]≡[p◾q]◾r {α} {A} {x} {y} {z} {w} p q r =
  (ind A
      (λ x y p → (z w : A) → (q : y ≡ z) → (r : z ≡ w) → p ◾ (q ◾ r) ≡ (p ◾ q) ◾ r)
      (λ x z w q r → (ind A
                          (λ y z q → (w : A) → (r : z ≡ w) → refl ◾ (q ◾ r) ≡ (refl ◾ q) ◾ r) 
                          (λ y w r → (ind A
                                          (λ z w r → refl ◾ (refl ◾ r) ≡ (refl ◾ refl) ◾ r)
                                          (λ _ → refl)
                                          y w r))
                          x z q) w r)
      x y p) z w q r

p◾[q◾r]≡[p◾q]◾r' : {α : Level} {A : Set α} → {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → p ◾ (q ◾ r) ≡ (p ◾ q) ◾ r
p◾[q◾r]≡[p◾q]◾r' {α} {A} {x} {y} {z} {w} refl refl refl = refl {α} {x ≡ x} {refl {α} {A} {x}}

-- Lemma 2.3.2

transport : {α β : Level} {A : Set α} → {x y : A} → (P : A → Set β) → (p : x ≡ y) → P x → P y
transport P refl q = q

lift : {α β : Level} {A : Set α} → {x y : A} → (P : A → Set β) → (u : P x) → (p : x ≡ y) → (x , u) ≡ (y , transport P p u)
lift P u refl = refl

-- EXERCISES

-- 1

{-
D : (A : Set) → (x y : A) → x ≡ y → Set
D A x y _ = (z : A) → y ≡ z → x ≡ z

E : (A : Set) → (x z : A) → (x ≡ z) → Set
E A x z _ = x ≡ z

d : (A : Set) → (x : A) → D A x x refl
d A x z p = ind A (λ x z _ → x ≡ z) (λ _ → refl) x z p
-}

-- induction on p
trans₂ : (A : Set) → (a b c : A) → a ≡ b → b ≡ c → a ≡ c
trans₂ A a b c p q = (ind A
                          (λ x y _ → (z : A) → y ≡ z → x ≡ z)
                          (λ _ _ r → r)
                          a b p) c q

-- induction on q
trans₃ : (A : Set) → (a b c : A) → a ≡ b → b ≡ c → a ≡ c
trans₃ A a b c p q = (ind A
                          (λ x y _ → (z : A) → z ≡ x → z ≡ y)
                          (λ _ _ r → r)
                          b c q) a p

-- Show the functions are pointwise equal when evaluated on all arguments.
-- Equality of functions then follows from iterated function extensionality.
-- Note that all three proofs are identical.

trans₁≡trans₂ : (A : Set) → (a b c : A) → (p : a ≡ b) → (q : b ≡ c) →
                trans₁ A a b c p q ≡ trans₂ A a b c p q
trans₁≡trans₂ A a b c p q = (ind A
                                 (λ a b p → (c : A) → (q : b ≡ c) → trans₁ A a b c p q ≡ trans₂ A a b c p q)
                                 (λ y z r → ind A
                                                (λ y z r →  trans₁ A y y z refl r ≡ trans₂ A y y z refl r)
                                                (λ _ → refl)
                                                y z r)
                                 a b p) c q

trans₁≡trans₃ : (A : Set) → (a b c : A) → (p : a ≡ b) → (q : b ≡ c) →
                trans₁ A a b c p q ≡ trans₃ A a b c p q
trans₁≡trans₃ A a b c p q = (ind A
                                 (λ a b p → (c : A) → (q : b ≡ c) → trans₁ A a b c p q ≡ trans₃ A a b c p q)
                                 (λ y z r → ind A
                                                (λ y z r →  trans₁ A y y z refl r ≡ trans₃ A y y z refl r)
                                                (λ _ → refl)
                                                y z r)
                                 a b p) c q

trans₂≡trans₃ : (A : Set) → (a b c : A) → (p : a ≡ b) → (q : b ≡ c) →
                trans₂ A a b c p q ≡ trans₃ A a b c p q
trans₂≡trans₃ A a b c p q = (ind A
                                 (λ a b p → (c : A) → (q : b ≡ c) → trans₂ A a b c p q ≡ trans₃ A a b c p q)
                                 (λ y z r → ind A
                                                (λ y z r →  trans₂ A y y z refl r ≡ trans₃ A y y z refl r)
                                                (λ _ → refl)
                                                y z r)
                                 a b p) c q

