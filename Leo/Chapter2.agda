{-# OPTIONS --without-K #-}

module Chapter2 where

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

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

sym : (A : Set) → (a b : A) → a ≡ b → b ≡ a
sym A a b p = ind A (λ x y _ → y ≡ x) (λ _ → refl) a b p

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
trans₁ A a b c p q = (ind A
                          (λ x y _ → (z : A) → y ≡ z → x ≡ z)
                          (λ x z r → ind A (λ x z _ → x ≡ z) (λ _ → refl) x z r)
                          a b p) c q

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

