{-# OPTIONS --without-K #-}

module Chapter2 where


transport : ∀ {α β} → {A : Set α} → {C : A → Set β} → (x y : A) → (p : x ≡ y) → C x ≡ C y
transport x .x refl = refl

sym : (A : Set) → (a b : A) → a ≡ b → b ≡ a
sym A a b p = ind A (λ x y _ → y ≡ x) (λ _ → refl) a b p

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

-- exercise 2.2
concat-commutes : (A : Set) → (a b c : A) → (p : a ≡ b) → (q : b ≡ c) →
  trans₁ (a ≡ c) (trans₁ A a b c p q) (trans₂ A a b c p q) (trans₃ A a b c p q)
  (trans₁≡trans₂ A a b c p q) (trans₂≡trans₃ A a b c p q)
  ≡ (trans₁≡trans₃ A a b c p q)
concat-commutes A a b c refl refl = refl

concat-commutes' : (A : Set) → (a b c : A) → (p : a ≡ b) → (q : b ≡ c) →
  trans₁ (a ≡ c) (trans₁ A a b c p q) (trans₂ A a b c p q) (trans₃ A a b c p q)
  (trans₁≡trans₂ A a b c p q) (trans₂≡trans₃ A a b c p q)
  ≡ (trans₁≡trans₃ A a b c p q)
concat-commutes' A a b c p q = {!
  ind A
  (λ a b p → (c : A) → (q : b ≡ c) →
    trans₁ (a ≡ c) (trans₁ A a b c p q) (trans₂ A a b c p q) (trans₃ A a b c p q)
      (trans₁≡trans₂ A a b c p q) (trans₂≡trans₃ A a b c p q)
      ≡ (trans₁≡trans₃ A a b c p q))
  (λ y z r →
    ind A
        (λ y z r →
          trans₁ (a ≡ c) (trans₁ A a b c p q) (trans₂ A a b c p q) (trans₃ A a b c p q)
          (trans₁≡trans₂ A a b c p q) (trans₂≡trans₃ A a b c p q)
          ≡ (trans₁≡trans₃ A a b c p q))
        (λ _ → refl)
        y z r)
        a b p) c q
  !}
