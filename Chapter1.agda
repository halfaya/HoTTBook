module Chapter1 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

