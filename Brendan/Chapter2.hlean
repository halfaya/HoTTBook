-- Section 2.1

local notation f ` $ `:1 a:0 := f a
local notation `⟨`a`,`b`⟩` := sigma.mk a b
local infixr ` ▸ `:75 := eq.subst

namespace ch2

variable {A : Type}

-- Lemma 2.1.1
lemma inverse_path : ∀ {x y : A}, (x = y) → (y = x)
| x x (eq.refl x) := eq.refl x
reveal inverse_path
postfix `⁻¹` := inverse_path

-- Lemma 2.1.2
lemma concat_path {x y z : A} : (x = y) → (y = z) → (x = z) :=
by intros h h'; induction h; induction h'; reflexivity
reveal concat_path
infix ` • `:60 := concat_path

definition concat_path_l {x y z : A} : (x = y) → (y = z) → (x = z) :=
by intros h h'; induction h; exact h'
reveal concat_path_l

definition concat_path_r {x y z : A} : (x = y) → (y = z) → (x = z) :=
by intros h h'; induction h'; exact h
reveal concat_path_r

-- Lemma 2.1.4
lemma refl_lunit_concat : ∀ {x y : A}, ∀ p : x = y, p = eq.refl x • p
| x x (eq.refl x) := eq.refl $ eq.refl x
reveal refl_lunit_concat
definition lu {x y : A} {p : x = y} : p = eq.refl x • p := refl_lunit_concat p

lemma refl_runit_concat : ∀ {x y : A}, ∀ p : x = y, p = p • eq.refl y
| x x (eq.refl x) := eq.refl $ eq.refl x
reveal refl_runit_concat
definition ru {x y : A} {p : x = y} : p = p • eq.refl y := refl_runit_concat p

lemma inv_concat : ∀ {x y : A}, ∀ p : x = y, p⁻¹ • p = eq.refl y
| x x (eq.refl x) := eq.refl $ eq.refl x
lemma concat_inv : ∀ {x y : A}, ∀ p : x = y, p • p⁻¹ = eq.refl x
| x x (eq.refl x) := eq.refl $ eq.refl x

lemma inv_inv : ∀ {x y : A}, ∀ p : x = y, (p⁻¹)⁻¹ = p
| x x (eq.refl x) := eq.refl $ eq.refl x

lemma concat_assoc : ∀ {w x y z : A}, ∀ (p : w = x) (q : x = y) (r : y = z), p • (q • r) = (p • q) • r
| x x x x (eq.refl x) (eq.refl x) (eq.refl x) := eq.refl $ eq.refl x

-- Remark 2.1.5
definition loop_space (a : A) := a = a
notation `Ω(`A`,`a`)` := @loop_space A a

definition loop_concat {a : A} : Ω(A, a) → Ω(A, a) → Ω(A, a) := concat_path
notation `Ω²(`A`,`a`)` := Ω(a = a, eq.refl a)

-- Theorem 2.1.6
section horizontal_composition
definition whisker_r : ∀ {a b c : A} {p q : a = b} (α : p = q) (r : b = c), p • r = q • r
| a b b p q α (eq.refl b) := (refl_runit_concat p)⁻¹ • α • refl_runit_concat q
infix ` •ᵣ `:60 := whisker_r

definition whisker_l : ∀ {a b c : A} {r s : b = c} (p : a = b) (β : r = s), p • r = p • s
| a a c r s (eq.refl a) β := (refl_lunit_concat r)⁻¹ • β • refl_lunit_concat s
infix ` •ₗ `:60 := whisker_l

variables {a : A} (α β : Ω²(a, A))

lemma whisker_r_refl : α = α •ᵣ rfl := refl_lunit_concat α • refl_runit_concat (rfl • α)
lemma whisker_l_refl : β = rfl •ₗ β := refl_lunit_concat β • refl_runit_concat (rfl • β)

definition horizontal_composition {a b c : A} {p q : a = b} {r s : b = c}
                                  (α : p = q) (β : r = s) := (α •ᵣ r) • (q •ₗ β)
infix ` ⋆ `:60 := horizontal_composition

lemma horizonatal_composition_eq_concat : α • β = α ⋆ β :=
  have h_α : α • (rfl •ₗ β) = (α •ᵣ rfl) • (rfl •ₗ β), from whisker_r_refl α ▸ rfl,
  have h_β : α • β          = α • (rfl •ₗ β),          from whisker_l_refl β ▸ rfl,
  show α • β = α ⋆ β, from h_β • h_α

definition horizontal_composition' {a b c : A} {p q : a = b} {r s : b = c}
                                   (α : p = q) (β : r = s) := (p •ₗ β) • (α •ᵣ s)
infix ` ⋆' `:60 := horizontal_composition'

lemma horizonatal_composition'_eq_reverse_concat : α ⋆' β = β • α :=
  have h_α : (rfl •ₗ β) • α = (rfl •ₗ β) • (α •ᵣ rfl), from whisker_r_refl α ▸ rfl,
  have h_β : β • α          = (rfl •ₗ β) • α,          from whisker_l_refl β ▸ rfl,
  show α ⋆' β = β • α, from (h_β • h_α)⁻¹

lemma horizontal_composition_eq_horizontal_composition' :
  ∀ {a b c : A} {p q : a = b} {r s : b = c} (α : p = q) (β : r = s), α ⋆ β = α ⋆' β :=
begin
  intros,
  induction p, induction α,
  induction r, induction β, 
  reflexivity
end

-- Theorem 2.1.6
lemma eckmann_hilton : α • β = β • α := horizonatal_composition_eq_concat α β •
                                        horizontal_composition_eq_horizontal_composition' α β •
                                        horizonatal_composition'_eq_reverse_concat α β

end horizontal_composition

-- Definition 2.1.7
definition pointed.{u} : Type.{u + 1} := Σ (A : Type.{u}), A

-- Definition 2.1.8
definition higher_loop_space : ℕ → pointed → pointed
| 0            ⟨A, a⟩ := ⟨A, a⟩
| (nat.succ n) ⟨A, a⟩ := higher_loop_space n ⟨Ω(A,a), eq.refl a⟩

namespace exercises

infix ` •₁ `:60 := concat_path 
infix ` •₂ `:60 := concat_path_l
infix ` •₃ `:60 := concat_path_r

-- Exercise 2.1
lemma concat_path_eq_concat_path_l : ∀ {a b c : A} (p : a = b) (q : b = c), p •₁ q = p •₂ q
| a a a (eq.refl a) (eq.refl a) := rfl
lemma concat_path_l_eq_concat_path_r : ∀ {a b c : A} (p : a = b) (q : b = c), p •₂ q = p •₃ q
| a a a (eq.refl a) (eq.refl a) := rfl
lemma concat_path_r_eq_concat_path : ∀ {a b c : A} (p : a = b) (q : b = c), p •₃ q = p •₁ q
| a a a (eq.refl a) (eq.refl a) := rfl

reveal concat_path_eq_concat_path_l
reveal concat_path_l_eq_concat_path_r
reveal concat_path_r_eq_concat_path

-- Exercise 2.2
lemma triangle : ∀ {a b c : A} (p : a = b) (q : b = c),
                 concat_path_eq_concat_path_l p q • concat_path_l_eq_concat_path_r p q = 
                 (concat_path_r_eq_concat_path p q)⁻¹
| a a a (eq.refl a) (eq.refl a) := rfl

-- Exercise 2.3
lemma concat_path_rev {x y z : A} : (x = y) → (y = z) → (x = z) :=
by intros h h'; induction h'; induction h; reflexivity
reveal concat_path_rev

lemma concat_path_rev_eq_concat_path : ∀ {a b c : A} (p : a = b) (q : b = c), concat_path_rev p q = concat_path p q
| a a a (eq.refl a) (eq.refl a) := rfl

-- Exercise 2.4
definition n_path (n : ℕ) (A : Type) : Type := nat.rec_on n A (λ k k_path , Σ (p q : k_path), p = q)

end exercises

end ch2
