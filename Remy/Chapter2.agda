{-# OPTIONS --without-K #-}

module Chapter2 where

-- Q what are these imports?

open import Agda.Primitive using (Level; lzero; lsuc)

infix 4 _≡_
data _≡_ {a : Level} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

-- Q why just Set not Set α?

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

-- Q what does this do?

{-# BUILTIN EQUALITY _≡_ #-}

ind : ∀ {α β} → (A : Set α) →
     (C : (x y : A) → x ≡ y → Set β) →
     ((x : A) → C x x refl) →
     (x y : A) → (p : x ≡ y) → C x y p
-- Q this is somewhat strange. on paper we can write
-- ind A C c x x, but here because of pattern match
-- one has to differentiate the names of the 2 xs.
-- I'm a bit surprised it still works.
ind A C c x .x refl = c x

ind' : ∀ {α β} → (A : Set α) →
       (a : A) →
       (C : (x : A) → a ≡ x → Set β) →
       C a refl →
       (x : A) → (p : a ≡ x) → C x p
ind' A a C c .a refl = c

----

-- how is this different from _≡_ above?

data Eq {α} (A : Set α) : A → A → Set α where
  refl : (x : A) → Eq A x x

indEq : ∀ {α β} → (A : Set α) →
     (C : (x y : A) → Eq A x y → Set β) →
     ((x : A) → C x x (refl x)) →
     (x y : A) → (p : Eq A x y) → C x y p
indEq A C c x .x (refl .x) = c x

-- Lemma 2.1.1

sym : (A : Set) → (a b : A) → a ≡ b → b ≡ a
sym A x y p = ind A (λ x y p → y ≡ x) (λ x → refl) x y p

_⁻¹ : {A : Set} → {a b : A} → a ≡ b → b ≡ a
_⁻¹ {A} {x} {y} p = sym A x y p

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
trans₁ A x y z p q = (ind A
                          (λ x y p → (z : A) → y ≡ z → x ≡ z)
                          (λ x → λ z q → ind A (λ x z r → x ≡ z) (λ x → refl) x z q)
                          x y p) z q

_●_ : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
_●_ {A} {x} {y} {z} p q = trans₁ A x y z p q

-- induction on p
trans₂ : (A : Set) → (a b c : A) → a ≡ b → b ≡ c → a ≡ c
trans₂ A x y z p q = (ind A
                          (λ x y p → (z : A) → y ≡ z → x ≡ z)
                          (λ x → λ z q → q)
                          x y p) z q

-- induction on q
trans₃ : (A : Set) → (a b c : A) → a ≡ b → b ≡ c → a ≡ c
trans₃ A x y z p q = (ind A
                          (λ y z q → (x : A) → x ≡ y → x ≡ z)
                          (λ y → λ x p → p)
                          y z q) x p

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
       (λ x → λ z w q r → (ind A
                               (λ x z q → (w : A) → (r : z ≡ w) → refl ● (q ● r) ≡ (refl ● q) ● r)
                               (λ x → λ w r → (ind A
                                                   (λ x w r → refl ● (refl ● r) ≡ (refl ● refl) ● r)
                                                   (λ x → refl)
                                                   x w r))
                               x z q) w r)
       x y p) z w q r

p●[q●r]≡[p●q]●r' : {A : Set} → {x y z w : A} → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w) → p ● (q ● r) ≡ (p ● q) ● r
p●[q●r]≡[p●q]●r' {A} {x} {y} {z} {w} refl refl refl = refl {lzero} {x ≡ x} {refl {lzero} {A} {x}}

-- Lemma 2.2.1

ap : {A B : Set} → {x y : A} → (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap {A} {B} {x} {y} f p
   = ind A
         (λ x y p → f x ≡ f y)
         (λ x → refl)
         x y p

-- Lemma 2.2.2.i

apfpqapfpapfq : {A B : Set} → {x y z : A} → (f : A → B) → (p : x ≡ y) → (q : y ≡ z) → ap f (p ● q) ≡ ap f p ● ap f q
apfpqapfpapfq {A} {B} {x} {y} {z} f p q
  = (ind A
         (λ x y p → (z : A) → (q : y ≡ z) → ap f (p ● q) ≡ (ap f p ● ap f q))
         (λ x → λ z q → (ind A
                           (λ x z q → ap f (refl ● q) ≡ ap f refl ● ap f q)
                           (λ x → refl)
                           x z q))
        x y p) z q

-- Lemma 2.2.2.ii

apfp-1≡apfp-1 : {A B : Set} → { x y : A } → {f : A → B} → {p : x ≡ y} → ap f (p ⁻¹) ≡ (ap f p) ⁻¹
apfp-1≡apfp-1 {A} {B} {x} {y} {f} {p}
  = (ind A
         (λ x y p → (f : A → B) → ap f (p ⁻¹) ≡ (ap f p) ⁻¹)
         (λ x → λ f → refl)
         x y p) f

-- Lemma 2.2.2.iii

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

apgapfp≡apg◦fp : {A B C : Set} → {x y z : A} → (f : A → B) → (g : B → C) → (p : x ≡ y) → ap g (ap f p) ≡ ap (g ∘ f) p
apgapfp≡apg◦fp {A} {B} {C} {x} {y} {z} f g p
  = (ind A
         (λ x y p → (f : A → B) → (g : B → C) → ap g (ap f p) ≡ ap (g ∘ f) p)
         (λ x → λ f g → refl) x y p) f g

id : (A : Set) → A → A
id A x = x

apidAp≡p : {A : Set} → {x y : A} → (p : x ≡ y) → ap (id A) p ≡ p
apidAp≡p {A} {x} {y} p = ind A (λ x y p → ap (id A) p ≡ p) (λ x → refl) x y p

-- Lemma 2.3.2

transport : {A : Set} → {x y : A} → (P : A → Set) → (p : x ≡ y) → P x → P y
transport P refl q = q

lift : {A : Set} → {x y : A} → (P : A → Set) → (u : P x) → (p : x ≡ y) → (x , u) ≡ (y , transport P p u)
lift P u refl = refl

-- Definition 2.4.1

_~_ : {A : Set} → {P : A → Set} → (f g : (x : A) → P x) → (x : A) → Set
_~_ {A} {P} f g x = f x ≡ g x

-- Lemma 2.4.2

-- f~f : {A : Set} → {P : A → Set} → (f : (x : A) → P x) → (f ~ f)

-- f~g→g~f :

-- f~g→g~h→f~h :

-- Lemma 2.4.3

Hx●gp≡fp●Hy : {A B : Set} → (x y : A) → (p : x ≡ y) → (f g : A → B) → (H x : (f ~ g) x) → (H x ● g p) ≡ (f p ● H y)
Hx●gp≡fp●Hy {A} {B} x y p f g H = ?
