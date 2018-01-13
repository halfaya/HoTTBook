{-# OPTIONS --without-K #-}

module Chapter2 where

open import Agda.Primitive using (Level; lzero; lsuc)

infix 4 _≡_
data _≡_ {a : Level} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

{-# BUILTIN EQUALITY _≡_ #-}

ind : ∀ {α β} → (A : Set α) →
     (C : (x y : A) → x ≡ y → Set β) →
     ((x : A) → C x x refl) →
     (x y : A) → (p : x ≡ y) → C x y p
ind A C c x .x refl = c x

ind' : ∀ {α β} → (A : Set α) →
       (a : A) → 
       (C : (x : A) → a ≡ x → Set β) →
       C a refl →
       (x : A) → (p : a ≡ x) → C x p
ind' A a C c .a refl = c

----

data Eq {α} (A : Set α) : A → A → Set α where
  refl : (x : A) → Eq A x x

indEq : ∀ {α β} → (A : Set α) →
     (C : (x y : A) → Eq A x y → Set β) →
     ((x : A) → C x x (refl x)) →
     (x y : A) → (p : Eq A x y) → C x y p
indEq A C c x .x (refl .x) = c x

-- Lemma 2.1.1

sym : (A : Set) → (a b : A) → a ≡ b → b ≡ a
sym A a b p = ind A (λ x y _ → y ≡ x) (λ _ → refl) a b p

_⁻¹ : {A : Set} → {a b : A} → a ≡ b → b ≡ a
_⁻¹ {A} {a} {b} p = sym A a b p

-- 1

{-
D : (A : Set) → (x y : A) → x ≡ y → Set
D A x y _ = (z : A) → y ≡ z → x ≡ z

E : (A : Set) → (x z : A) → (x ≡ z) → Set
E A x z _ = x ≡ z

d : (A : Set) → (x : A) → D A x x refl
d A x z p = ind A (λ x z _ → x ≡ z) (λ _ → refl) x z p
-}

-- induction on p and then q
trans₁ : (A : Set) → (a b c : A) → a ≡ b → b ≡ c → a ≡ c
--trans₁ A _ _ _ refl refl = refl
trans₁ A a b c p q = (ind A
                          (λ x y _ → (z : A) → y ≡ z → x ≡ z)
                          (λ x z r → ind A (λ x z _ → x ≡ z) (λ _ → refl) x z r)
                          a b p) c q

_●_ : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
_●_ {A} {a} {b} {c} p q = trans₁ A a b c p q

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

-- Lemma 2.1.4(i)

p≡p●refl : {A : Set} → {x y : A} → (p : x ≡ y) → p ≡ p ● refl {lzero} {A} {y}
p≡p●refl {A} {x} {y} p = ind A
                             (λ a b q → q ≡ q ● refl {lzero} {A} {b})
                             (λ c → refl {lzero} {_≡_ {lzero} {A} c c} {refl {lzero} {A} {c}})
                             x y p

p≡refl●p : {A : Set} → {x y : A} → (p : x ≡ y) → p ≡ refl {lzero} {A} {x} ● p
p≡refl●p {A} {x} {y} p = ind A
                             (λ a b q → q ≡ refl {lzero} {A} {a} ● q)
                             (λ c → refl {lzero} {_≡_ {lzero} {A} c c} {refl {lzero} {A} {c}})
                             x y p

-- Lemma 2.1.4(ii)

p⁻¹●p≡refl : {A : Set} → {x y : A} → (p : x ≡ y) → (p ⁻¹) ● p ≡ refl {lzero} {A} {y}
p⁻¹●p≡refl {A} {x} {y} p = ind A
                               (λ a b q → (q ⁻¹) ● q ≡ refl {lzero} {A} {b})
                               (λ c → refl {lzero} {c ≡ c} {refl {lzero} {A} {c}})
                               x y p

p●p⁻¹≡refl : {A : Set} → {x y : A} → (p : x ≡ y) → p ● (p ⁻¹) ≡ refl {lzero} {A} {x}
p●p⁻¹≡refl {A} {x} {y} p = ind A
                               (λ a b q → q ● (q ⁻¹) ≡ refl {lzero} {A} {a})
                               (λ c → refl {lzero} {c ≡ c} {refl {lzero} {A} {c}})
                               x y p

-- Lemma 2.1.4(iii)

p⁻¹⁻¹≡p : {A : Set} → {x y : A} → (p : x ≡ y) → (p ⁻¹) ⁻¹ ≡ p
p⁻¹⁻¹≡p {A} {x} {y} p = ind A
                            (λ _ _ p → (p ⁻¹) ⁻¹ ≡ p)
                            (λ _ → refl)
                            x y p

-- Lemma 2.1.4(iv)

p●[q●r]≡[p●q]●r : {A : Set} → {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → p ● (q ● r) ≡ (p ● q) ● r
p●[q●r]≡[p●q]●r {A} {x} {y} {z} {w} p q r =
  (ind A
      (λ x y p → (z w : A) → (q : y ≡ z) → (r : z ≡ w) → p ● (q ● r) ≡ (p ● q) ● r)
      (λ x z w q r → (ind A
                          (λ y z q → (w : A) → (r : z ≡ w) → refl ● (q ● r) ≡ (refl ● q) ● r) 
                          (λ y w r → (ind A
                                          (λ z w r → refl ● (refl ● r) ≡ (refl ● refl) ● r)
                                          (λ _ → refl)
                                          y w r))
                          x z q) w r)
      x y p) z w q r

p●[q●r]≡[p●q]●r' : {A : Set} → {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → p ● (q ● r) ≡ (p ● q) ● r
p●[q●r]≡[p●q]●r' {A} {x} {y} {z} {w} refl refl refl = refl {lzero} {x ≡ x} {refl {lzero} {A} {x}}

-- Lemma 2.3.2

transport : {A : Set} → {x y : A} → (P : A → Set) → (p : x ≡ y) → P x → P y
transport P refl q = q

lift : {A : Set} → {x y : A} → (P : A → Set) → (u : P x) → (p : x ≡ y) → (x , u) ≡ (y , transport P p u)
lift P u refl = refl
