{-# OPTIONS --without-K #-}

module Chapter1 where

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

cong : {A B : Set} → {a a' : A} → (f : A → B) → a ≡ a' → f a ≡ f a'
cong f refl = refl

{-# BUILTIN EQUALITY _≡_ #-}


-- 1

infixr 9 _∘_

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ f = λ a → g (f a)

∘assoc : {A B C D : Set} → {f : A → B} → {g : B → C} → {h : C → D} → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘assoc = refl

etaEquality : {A B : Set} → {f : A → B} → f ≡ λ x → f x
etaEquality = refl

-- 2

infixr 2 _×_
infixr 4 _,_

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

π₁ : {A B : Set} → A × B → A
π₁ (a , _) = a

π₂ : {A B : Set} → A × B → B
π₂ (_ , b) = b

rec× : {A B C : Set} → (A → B → C) → A × B → C
rec× g ab = g (π₁ ab) (π₂ ab)

pr₁ : {A B : Set} → A × B → A
pr₁ = rec× (λ a _ → a)

pr₂ : {A B : Set} → A × B → B
pr₂ = rec× (λ _ b → b)

π₁≡pr₁ : {A B : Set} → {ab : A × B} → π₁ ab ≡ pr₁ ab
π₁≡pr₁ = refl

π₂≡pr₂ : {A B : Set} → {ab : A × B} → π₂ ab ≡ pr₂ ab
π₂≡pr₂ = refl

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

proj₁ : {A : Set} → {B : A → Set} → Σ A B → A
proj₁ (a , _) = a

proj₂ : {A : Set} → {B : A → Set} → (ab : Σ A B) → B (proj₁ ab)
proj₂ (_ , b) = b

recΣ : {A C : Set} → {B : A → Set} → ((a : A) → B a → C) → Σ A B → C
recΣ g ab = g (proj₁ ab) (proj₂ ab)

p₁ : {A : Set} → {B : A → Set} → Σ A B → A
p₁ = recΣ (λ a _ → a)

p₂ : {A : Set} → {B : A → Set} → (ab : Σ A B) → B (proj₁ ab)
p₂ ab@(a , b) = recΣ (λ x y → {!!}) ab

proj₁≡p₁ : {A : Set} → {B : A → Set} → {ab : Σ A B} → proj₁ ab ≡ p₁ ab
proj₁≡p₁ = refl

proj₂≡p₂ : {A : Set} → {B : A → Set} → {ab : Σ A B} → proj₂ ab ≡ p₂ ab
proj₂≡p₂ = {!!}

-- 3

uniq× : {A B : Set} → {ab : A × B} → (π₁ ab , π₂ ab) ≡ ab
uniq× {ab = (_ , _)} = refl

ind× : {A B : Set} → {C : A × B → Set} → ((a : A) → (b : B) → C (a , b)) → (ab : A × B) → C ab
ind× g ab@(_ , _) = g (π₁ ab) (π₂ ab)

-- 4

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

natRec : {C : Set} → C → (ℕ → C → C) → ℕ → C
natRec z s zero    = z
natRec z s (suc n) = s n (natRec z s n)

natIter : {C : Set} → C → (C → C) → ℕ → C
natIter z s zero    = z
natIter z s (suc n) = s (natIter z s n)

pred : ℕ → ℕ
pred zero    = zero
pred (suc n) = n

natRec' : {C : Set} → C → (ℕ → C → C) → ℕ → C
natRec' z s n = natIter z (s (pred n)) n

rec≡rec' : {C : Set} → (z : C) → (s : (ℕ → C → C))  → (n : ℕ) → natRec z s n ≡ natRec' z s n
rec≡rec' z s zero    = refl
rec≡rec' z s (suc n) = let x = rec≡rec' z s n in cong (s n) {!!}

-- 5

data Bool : Set where
  false : Bool
  true  : Bool

boolRec : ∀{ℓ} → {C : Set ℓ} → C → C → Bool → C
boolRec f t false = f
boolRec f t true  = t

infixr 1 _+_ _⊕_

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

ind+ : {A B : Set} → {C : A + B → Set} → ((a : A) → C (inl a)) → ((b : B) → C (inr b)) → (x : A + B) → C x
ind+ g₀ g₁ (inl a) = g₀ a
ind+ g₀ g₁ (inr b) = g₁ b

_⊕_ : (A B : Set) → Set
A ⊕ B = Σ Bool (λ x -> boolRec A B x)

in1 : {A B : Set} → A → A ⊕ B
in1 a = false , a

in2 : {A B : Set} → B → A ⊕ B
in2 b = true , b

ind⊕ : {A B : Set} → {C : A ⊕ B → Set} → ((a : A) → C (in1 a)) → ((b : B) → C (in2 b)) → (x : A ⊕ B) → C x
ind⊕ g₀ g₁ (false , a) = g₀ a
ind⊕ g₀ g₁ (true  , b) = g₁ b

-- 6

_⊗_ : (A B : Set) → Set
A ⊗ B = (x : Bool) → boolRec A B x

pi1 : {A B : Set} → A ⊗ B → A
pi1 ab = ab false

pi2 : {A B : Set} → A ⊗ B → B
pi2 ab = ab true

_·_ : {A B : Set} → A → B → A ⊗ B
(a · b) false = a
(a · b) true  = b

postulate
  function-extensionality : {A : Set} → {B : A → Set} → {f g : (a : A) → B a} → ((x : A) → f x ≡ g x) → f ≡ g

uniq⊗i : {A B : Set} → {ab : A ⊗ B} → (x : Bool) → (pi1 ab · pi2 ab) x ≡ ab x
uniq⊗i false = refl
uniq⊗i true  = refl

uniq⊗ : {A B : Set} → {ab : A ⊗ B} → pi1 ab · pi2 ab ≡ ab
uniq⊗ = function-extensionality uniq⊗i

ind⊗ : {A B : Set} → {C : A ⊗ B → Set} → ((a : A) → (b : B) → C (a · b)) → (x : A ⊗ B) → C x
ind⊗ {A} {B} g ab rewrite (uniq⊗ {A} {B} {ab}) = {!!} -- g (pi1 ab) (pi2 ab)

