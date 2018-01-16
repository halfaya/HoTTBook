-- Section 2.1 From the HoTT Book

module Sec2-1 where

open import Agda.Primitive
  using (lsuc; lzero)
open import Common


{- The groupoid structure of a type A -}

-- Lemma 2.1.1: existence of inverses
inverse : ∀ {α} → {A : Set α} → {x y : A} → (x ≡ y) → (y ≡ x)
inverse refl = refl

-- Lemma 2.1.2: existence of composite
infixr 15 _·_
_·_ : ∀ {α} → {A : Set α} → {x y z : A} → (x ≡ y) → (y ≡ z) → (x ≡ z)
refl · refl = refl

-- Lemma 2.1.4: the type `x = y` forms a group
refl-left : ∀ {α} → {A : Set α} → {x y : A} → (p : x ≡ y) → refl · p ≡ p
refl-left refl = refl

refl-right : ∀ {α} → {A : Set α} → {x y : A} → (p : x ≡ y) → p · refl ≡ p
refl-right refl = refl

inverse-left : ∀ {α} → {A : Set α} → {x y : A} → (p : x ≡ y) → inverse p · p ≡ refl
inverse-left refl = refl

inverse-right : ∀ {α} → {A : Set α} → {x y : A} → (p : x ≡ y) → p · inverse p ≡ refl
inverse-right refl = refl

compose-assoc : ∀ {α} → {A : Set α} → {x y z w : A}
                  → (p : x ≡ y) → (q : y ≡ z) → (r : z ≡ w)
                  → p · q · r ≡ (p · q) · r
compose-assoc refl refl refl = refl

-- Theorem 2.1.6 (Eckmann-Hilton): Ω²(A) is abelian
-- implement Ωⁿ(A,a) using the equality type
Ω : ∀ {α} → (A : Set α) → {a : A} → (n : ℕ) → Set α
Ω {α} A {a} zero = A
Ω {α} A {a} (succ n) = Ω {α} (a ≡ a) {refl} n

-- composition of 2-loops
wisker-right : ∀ {ℓ} → {A : Set ℓ} → {a b c : A} → {p q : a ≡ b} → (α : p ≡ q) → (r : b ≡ c) → p · r ≡ q · r
wisker-right {ℓ} {A} {a} {b} {c} {p} {q} α refl = (refl-right p) · α · (inverse (refl-right q))

wisker-left : ∀ {ℓ} → {A : Set ℓ} → {a b c : A} → {r s : b ≡ c} → (β : r ≡ s) → (p : a ≡ b) → p · r ≡  p · s
wisker-left {ℓ} {A} {a} {b} {c} {r} {s} β refl = (refl-left r) · β · (inverse (refl-left s))

h-compose : ∀ {ℓ} → {A : Set ℓ} → {a b c : A} → {p q : a ≡ b} → {r s : b ≡ c} →
                 (α : p ≡ q) → (β : r ≡ s) → p · r ≡ q · s
h-compose {ℓ} {A} {a} {b} {c} {p} {q} {r} {s} α β = (wisker-right α r) · (wisker-left β q)

h-compose' : ∀ {ℓ} → {A : Set ℓ} → {a b c : A} → {p q : a ≡ b} → {r s : b ≡ c} →
                 (α : p ≡ q) → (β : r ≡ s) → p · r ≡ q · s
h-compose' {ℓ} {A} {a} {b} {c} {p} {q} {r} {s} α β = (wisker-left β p) · (wisker-right α s)

h-compose-agree : ∀ {ℓ} → {A : Set ℓ} → {a b c : A} → {p q : a ≡ b} → {r s : b ≡ c} →
                 (α : p ≡ q) → (β : r ≡ s) → h-compose α β ≡ h-compose' α β
h-compose-agree {ℓ} {A} {.b} {b} {.b} {refl} {.refl} {refl} {.refl} refl refl = refl

h-compose-eq : ∀ {ℓ} → {A : Set ℓ} → {a : A} → (α β : Ω A {a} 2) →
               h-compose {ℓ} {A} {a} {a} {a} {refl} {refl} {refl} {refl} α β ≡ α · β
h-compose-eq α β =
  let bcdef : (α · refl) · refl · β · refl ≡ α · refl · refl · β · refl
      bcdef = inverse (compose-assoc α refl (refl · (β · refl)))
      bcdef' : refl · (α · refl) · refl · β · refl ≡ refl · α · refl · refl · β · refl
      bcdef' = wisker-left bcdef refl
      abcdef : refl · (α · refl) · refl · β · refl ≡ (refl · α · refl) · refl · β · refl
      abcdef = compose-assoc refl (α · refl) (refl · β · refl)
      rest = (wisker-left (wisker-left ((wisker-left ((wisker-left (refl-right β) refl) · (refl-left β)) refl) · (refl-left β)) α) refl) · (refl-left (α · β))
  in ((inverse abcdef) · bcdef') · rest

h-compose'-eq : ∀ {ℓ} → {A : Set ℓ} → {a : A} → (α β : Ω A {a} 2) →
                h-compose' {ℓ} {A} {a} {a} {a} {refl} {refl} {refl} {refl} α β ≡ β · α
h-compose'-eq α β = ((wisker-left (wisker-left (refl-right α) refl) (refl · β · refl)))
                  · (compose-assoc (refl · β · refl) refl α)
                  · (wisker-right ((wisker-right ((wisker-left (refl-right β) refl) · (refl-left β)) refl) · (refl-right β)) α)

eckmann-hilton :  ∀ {ℓ} → {A : Set ℓ} → {a : A} → (α β : Ω A {a} 2) → α · β ≡ β · α
eckmann-hilton {ℓ} {A} {a} α β =
  let p1 : h-compose {ℓ} {A} {a} {a} {a} {refl} {refl} {refl} {refl} α β ≡ α · β
      p1 = h-compose-eq α β
      p2 : h-compose' α β ≡ β · α
      p2 = h-compose'-eq α β
  in inverse p1 · h-compose-agree α β · p2


