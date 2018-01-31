local notation f ` $ `:1 a:0 := f a
local notation `⟨`a`,`b`⟩` := sigma.mk a b
local notation `(`a`,`b`)` := prod.mk a b
local infixr ` ∘ `:60 := function.compose

namespace ch2

variable {A : Type}

-- Lemma 2.3.1
-- We define this early so we have access to it in the horizontal composition section
definition transport {P : A → Type} : ∀ {x y : A}, x = y → P x → P y
| x x (eq.refl x) := id
infix `∗`:60 := transport

section one
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
  have h_α : α • (rfl •ₗ β) = (α •ᵣ rfl) • (rfl •ₗ β), from (whisker_r_refl α) ∗ rfl,
  have h_β : α • β          = α • (rfl •ₗ β),          from (whisker_l_refl β) ∗ rfl,
  show α • β = α ⋆ β, from h_β • h_α

definition horizontal_composition' {a b c : A} {p q : a = b} {r s : b = c}
                                   (α : p = q) (β : r = s) := (p •ₗ β) • (α •ᵣ s)
infix ` ⋆' `:60 := horizontal_composition'

lemma horizonatal_composition'_eq_reverse_concat : α ⋆' β = β • α :=
  have h_α : (rfl •ₗ β) • α = (rfl •ₗ β) • (α •ᵣ rfl), from whisker_r_refl α ∗ rfl,
  have h_β : β • α          = (rfl •ₗ β) • α,          from whisker_l_refl β ∗ rfl,
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
definition higher_loop_space.{u} : ℕ → pointed.{u} → pointed.{u}
| 0            ⟨A, a⟩ := ⟨A, a⟩
| (nat.succ n) ⟨A, a⟩ := higher_loop_space n ⟨Ω(A,a), eq.refl a⟩

end one

section two
variables {B C : Type} (f : A → B) (g : B → C)

-- Lemma 2.2.1
definition ap : ∀ {x y}, x = y → f x = f y
| x x (eq.refl x) := eq.refl $ f x
notation function`[`equality`]` := ap function equality

-- Lemma 2.2.2
lemma distribute_ap_concat_path : ∀ {x y z} (p : x = y) (q : y = z), f[p • q] = f[p] • f[q]
| x x x (eq.refl x) (eq.refl x) := eq.refl $ eq.refl $ f x

lemma ap_commutes_with_inverse : ∀ {x y} (p : x = y), f[p⁻¹] = f[p]⁻¹
| x x (eq.refl x) := eq.refl $ eq.refl $ f x

lemma composition_commutes_with_ap : ∀ {x y} (p : x = y), (ap g ∘ ap f) p = ap (g ∘ f) p
| x x (eq.refl x) := eq.refl $ eq.refl $ g ∘ f $ x

lemma ap_id_eq_id : ∀ {x y} (p : x = y), ap (@id A) p = @id (x = y) p
| x x (eq.refl x) := eq.refl $ eq.refl x

end two

section three

variables {P : A → Type} {B : Type}

-- See the top of this file for Lemma 2.3.1

-- Lemma 2.3.2
definition lift : ∀ {x y : A} (p : x = y) (u : P x), ⟨x, u⟩ = ⟨y, p∗u⟩
| x x (eq.refl x) u := rfl
lemma pr1_lift_eq_p : ∀ {x y : A} (p : x = y) (u : P x), sigma.pr1[lift p u] = p
| x x (eq.refl x) u := rfl

-- Lemma 2.3.4
definition apd (f : A → B) : ∀ {x y}, Π p : x = y, p∗(f x) = f y
| x x (eq.refl x) := rfl

-- Lemma 2.3.5
definition transportconst : ∀ {x y : A}, Π (p : x = y) (b : B), @transport A (λ a, B) x y p b = b
| x x (eq.refl x) b := rfl

-- Definition 2.3.6
lemma nondep_eq_implies_transport_eq (f : A → B) {x y} (p : x = y) : f x = f y → p∗(f x) = f y :=
  eq.cases_on p (λ pf, pf)

-- Definition 2.3.7
lemma transport_eq_implies_nondep_eq (f : A → B) {x y} (p : x = y) : p∗(f x) = f y → f x = f y :=
  eq.cases_on p (λ pf, pf)

-- Definition 2.3.8
lemma apd_eq_transportconst_concat_ap (f : A → B) : ∀ {x y} (p : x = y),
  apd f p = transportconst p (f x) • ap f p
| x x (eq.refl x) := rfl

-- Lemma 2.3.9
definition transport_q_tranport_p
  : ∀ {x y z : A} (p : x = y) (q : y = z) (u : P x), q∗(p∗u) = (p•q)∗u
| x x x (eq.refl x) (eq.refl x) u := rfl

-- Lemma 2.3.10
definition transport_across_comp_eq_transport_ap (f : A → B)
  {P : B → Type}
  : ∀ {x y} (p : x = y) (u : P $ f x), p∗u = f[p]∗u
| x x (eq.refl x) u := rfl

-- Lemma 2.3.11
definition transport_fx_u_eq_fy_transport_u
  {Q : A → Type} (f : Π x, P x → Q x)
  : ∀ {x y} (p : x = y) (u : P x), p∗(f x u) = f y (p∗u)
| x x (eq.refl x) u := rfl

end three

section four

variables {P : A → Type} {B : Type}

-- Definition 2.4.1
definition homotopy (f g : Π x, P x) := Π x, f x = g x
infix `~` := homotopy

-- Lemma 2.4.2
lemma homotopy_refl (f : Π x, P x) : f ~ f := λ x, rfl
lemma homotopy_symm (f g : Π x, P x) : f ~ g → g ~ f :=
  λ homotopy, λ x, (homotopy x)⁻¹
lemma homotopy_trans (f g h : Π x, P x) : f ~ g → g ~ h → f ~ h :=
  λ homotopy₁ homotopy₂, λ x, homotopy₁ x • homotopy₂ x

-- Lemma 2.4.3
/-
             f[p]
      f(x) ======== f(y)
       ||           ||
       ||           ||
  H(x) ||           || H(y)
       ||           ||
       ||           ||
      g(x) ======== g(y)
             g[p]
-/
lemma homotopy_is_natural_transformation {f g : A → B} (H : f ~ g)
  : Π {x y : A} (p : x = y), H(x) • g[p] = f[p] • H(y)
| x x (eq.refl x) :=
  calc H(x) • g[eq.refl x] = H(x) • eq.refl (g x) : rfl
       ...                 = H(x)                 : ru⁻¹
       ...                 = eq.refl (f x) • H(x) : lu
       ...                 = f[eq.refl x] • H(x)  : rfl

-- Corollary 2.4.4
lemma homotopy_id (f : A → A) (H : f ~ id) (x : A) : H (f x) = f [H x] :=
  calc H (f x) = H (f x) • rfl               : ru
       ...     = H (f x) • (H x • (H x)⁻¹)   : (H (f x) •ₗ !concat_inv)⁻¹
       ...     = H (f x) • H x • (H x)⁻¹     : !concat_assoc
       ...     = H (f x) • id[H x] • (H x)⁻¹ : { (ap_id_eq_id (H x))⁻¹ }
       ...     = f[H x] • H x • (H x)⁻¹      : homotopy_is_natural_transformation H (H x) •ᵣ (H x)⁻¹
       ...     = f[H x] • (H x • (H x)⁻¹)    : !concat_assoc⁻¹
       ...     = f[H x] • rfl                : f[H x] •ₗ !concat_inv
       ...     = f[H x]                      : ru⁻¹

-- Defintions 2.4.5-6
definition quasi_inverse (f : A → B) := Σ g, f ∘ g ~ id × g ∘ f ~ id
definition qinv (f : A → B) := quasi_inverse f

-- Examples 2.4.7-9
example : qinv (@id A) := ⟨id, (λ x, eq.refl x, λ y, eq.refl y)⟩
lemma p_concat_comp_p_inv_concat_homotopic_id {x y : A} (p : x = y)
  : ∀ z, (λ q : y = z, p • q) ∘ (λ q : x = z, p⁻¹ • q) ~ id :=
  λ z r, calc p • (p⁻¹ • r) = (p • p⁻¹) • r : !concat_assoc
              ...           = rfl • r       : !concat_inv •ᵣ r
              ...           = r             : lu⁻¹
lemma p_inv_concat_comp_p_concat_homotopic_id {x y : A} (p : x = y)
  : ∀ z, (λ q : x = z, p⁻¹ • q) ∘ (λ q : y = z, p • q) ~ id :=
  eq.subst (inv_inv p) $ p_concat_comp_p_inv_concat_homotopic_id p⁻¹
lemma concat_p_comp_concat_p_inv_homotopic_id {x y : A} (p : x = y)
  : ∀ z, (λ q : z = x, q • p) ∘ (λ q : z = y, q • p⁻¹) ~ id :=
  λ z r, calc r • p⁻¹ • p = r • (p⁻¹ • p) : !concat_assoc
              ...         = r • rfl       : r •ₗ inv_concat p
              ...         = r             : ru⁻¹

lemma concat_p_inv_comp_concat_p_homotopic_id {x y : A} (p : x = y)
  : ∀ z, (λ q : z = y, q • p⁻¹) ∘ (λ q : z = x, q • p) ~ id :=
  eq.subst (inv_inv p) $ concat_p_comp_concat_p_inv_homotopic_id p⁻¹
example {x y : A} (p : x = y) : ∀ z : A, qinv (λ q : y = z, p • q) :=
  λ z, ⟨λ q, p⁻¹ • q,
        (p_concat_comp_p_inv_concat_homotopic_id p z,
         p_inv_concat_comp_p_concat_homotopic_id p z)⟩
example {x y : A} (p : x = y) : ∀ z : A, qinv (λ q : z = x, q • p) :=
  λ z, ⟨λ q, q • p⁻¹,
        (concat_p_comp_concat_p_inv_homotopic_id p z,
         concat_p_inv_comp_concat_p_homotopic_id p z)⟩
example {P : A → Type} {x y : A} (p : x = y) : qinv (@transport A P x y p) :=
  ⟨transport p⁻¹, eq.cases_on p (λ z, rfl, λ z, rfl)⟩

-- Definition 2.4.10
definition isequiv (f : A → B) := (Σ g, f ∘ g ~ id) × (Σ h, h ∘ f ~ id)
definition qinv2isequiv {f : A → B} : qinv f → isequiv f
| ⟨g, (α, β)⟩ := (⟨g, α⟩, ⟨g, β⟩)
definition isequiv2qinv {f : A → B} : isequiv f → qinv f
| (⟨g, α⟩, ⟨h, β⟩) := ⟨g, (α,
  let γ : g ~ h := λ x, (β (g x))⁻¹ • h[α x] in
  show g ∘ f ~ id, from λ x, γ (f x) • β x
)⟩
definition isequiv_singleton (f : A → B) : Π x y : isequiv f, x = y :=
  sorry

definition equivalence [reducible] A B := Σ f : A → B, isequiv f
local notation X` ≃ `Y := equivalence X Y

-- Lemma 2.4.12
lemma equivalence_refl (A) : A ≃ A :=
  ⟨id, (⟨id, λ x, rfl⟩, ⟨id, λ x, rfl⟩)⟩
lemma equivalence_symm (A B) : A ≃ B → B ≃ A
| ⟨f, is_equiv_f⟩ :=
  match isequiv2qinv is_equiv_f with
  | ⟨g, (α, β)⟩ := ⟨g, qinv2isequiv ⟨f, (β, α)⟩⟩
  end
lemma equivalence_trans (A B C) : A ≃ B → B ≃ C → A ≃ C
| ⟨fAB, is_equiv_fAB⟩ ⟨fBC, is_equiv_fBC⟩ :=
  match isequiv2qinv is_equiv_fAB with
  | ⟨gBA, (αAB, βAB)⟩ :=
    match isequiv2qinv is_equiv_fBC with
    | ⟨gCB, (αBC, βBC)⟩ :=
            have forwards_homotopy : ((fBC ∘ fAB) ∘ gBA ∘ gCB) ~ id,
            from λx,
            calc ((fBC ∘ fAB) ∘ gBA ∘ gCB) x = fBC (fAB (gBA (gCB x))) : rfl
            ... = fBC (id (gCB x)) : {αAB (gCB x)}
            ... = id x             : {αBC x},
            have backwards_homotopy : ((gBA ∘ gCB) ∘ fBC ∘ fAB) ~ id,
            from λx,
            calc ((gBA ∘ gCB) ∘ fBC ∘ fAB) x = gBA (gCB (fBC (fAB x))) : rfl
            ... = gBA (id (fAB x)) : {βBC (fAB x)}
            ... = id x             : {βAB x},
            have qinv_composition : qinv (fBC ∘ fAB),
            from ⟨gBA ∘ gCB, (forwards_homotopy, backwards_homotopy)⟩,
            show A ≃ C, from ⟨fBC ∘ fAB, qinv2isequiv qinv_composition⟩
    end
  end

end four

section six

variable {B : Type}

-- 2.6.1
definition prod_eq2components_eq : ∀ {x y : A × B}, x = y
  → prod.pr1 x = prod.pr1 y × prod.pr2 x = prod.pr2 y :=
  λ x y p, (prod.pr1[p], prod.pr2[p])

-- Theorem 2.6.2
definition eq.pair {a a' : A} {b b' : B} : a = a' × b = b' → (a, b) = (a', b')
| (q, r) := eq.cases_on q $ eq.cases_on r rfl
notation `pair⁼` := eq.pair

definition prod.uniqueness
  : Π (x : A × B), x = (prod.pr1 x, prod.pr2 x) :=
  prod.rec (λ a b, eq.refl (a, b))

definition eq.pair_comp_prod_eq2components_eq_homotopic_id_uptop_transport : Π {x y : A × B} (r : x = y), (pair⁼ ∘ prod_eq2components_eq) r =
  transport (prod.uniqueness y)
  (transport (prod.uniqueness x) r)
| x x (eq.refl x) :=
  match x with
  | (a, b) := eq.refl (eq.refl (a, b))
  end

theorem components_eq_is_equivalence
  : Π {x y : A × B}, isequiv (@prod_eq2components_eq A B x y)
| (a, b) (a', b') :=
  have forwards_homotopy : Π s : a = a' × b = b', (prod_eq2components_eq ∘ pair⁼) s = id s,
  from λ s, prod.cases_on s (λ p q, eq.cases_on p (eq.cases_on q rfl)),
  have backwards_homotopy : Π r : (a, b) = (a', b'), pair⁼ (prod_eq2components_eq r) = id r,
  from eq.pair_comp_prod_eq2components_eq_homotopic_id_uptop_transport,
  show isequiv (@prod_eq2components_eq A B (a, b) (a', b')),
  from qinv2isequiv ⟨pair⁼, (forwards_homotopy, backwards_homotopy)⟩

-- Theorem 2.6.4
theorem transport_pair_eq_pair_transport {P Q : A → Type}
  : Π {a b : A} (p : a = b) (x : P a × Q a),
  p∗x = (p ∗ prod.pr1 x, p ∗ prod.pr2 x)
| a a (eq.refl a) (pa, qa) := eq.refl (pa, qa)

-- Theorem 2.6.5
definition pair_functions {A' B'} (g : A → A') (h : B → B') : A × B → A' × B'
| (a, b) := (g a, h b)

theorem ap_pair_fn_commutes_eq.pair {A' B'} (g : A → A') (h : B → B')
  : Π {x y : A × B},
    Π (p : prod.pr1 x = prod.pr1 y) (q : prod.pr2 x = prod.pr2 y),
    ap (pair_functions g h) (pair⁼ (p, q)) = pair⁼ (g[p], h[q])
| (a, b) (a, b) (eq.refl a) (eq.refl b) := rfl

end six

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

-- Exercise 2.14
--axiom

definition equ_reflection {K : ∀ {A : Type} {a : A} {C : a = a → Type},  C rfl → Π loop : a = a, C loop} {x : A} (p : x = x) : p = rfl :=
K rfl p

end exercises

end ch2

-- To be justified in using lean's `calc` expressions, I need to know that my definitions agree with theirs
namespace sanity_check

theorem concat_good {A} : ∀ {x y z : A} (p : x = y) (q : y = z), ch2.concat_path p q = eq.trans p q
| x x x (eq.refl x) (eq.refl x) := rfl

theorem transport_good {A} {P : A → Type} : ∀ {x y} (p : x = y) (u : P x), ch2.transport p u = eq.subst p u
| x x (eq.refl x) u := rfl

end sanity_check
