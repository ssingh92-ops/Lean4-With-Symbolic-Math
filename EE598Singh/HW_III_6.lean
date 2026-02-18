/-
HW_III_6.lean — EE598
Sukhman Singh

Instructions (from slide deck):
- Put solutions in HW_III_6.lean in the same directory as Basic.lean.
- Restate each problem.
- Textual answers should be written as comments.
- Lean code should produce no errors (sorry is allowed for partial credit).
-/
import mathlib


/-
-- ============================================================
-- III.6 Exercise 1
-- Exercise 1 — MyEq.to_iff
-- Problem (restated):
--   Prove the `to_iff` theorem for `MyEq`:
--     if `a ~ b` for propositions `a b : Prop`, then `a ↔ b`.
--
-- Context:
--   `MyEq` is our custom equality (with constructor `refl`) and we have:
--     MyEq.subst : a ~ b → P a → P b
--
-- Proof idea:
--   Use substitution with the motive `P := fun p => (a ↔ p)`.
--   We already have `Iff.rfl : a ↔ a`, and substituting along `a ~ b`
--   yields `a ↔ b`.
-- ============================================================
-/

-- setup
universe u

inductive MyEq {α : Sort u} : α → α → Prop where
  | refl (a : α) : MyEq a a

infix:50 " ~ " => MyEq
infix:50 " ∼ " => MyEq

theorem MyEq.subst {α : Sort u} {P : α → Prop} {a b : α}
                   (h₁ : a ~ b) (h₂ : P a) : P b := by
  cases h₁ with
  | refl => exact h₂

-- solution
theorem MyEq.to_iff (a b : Prop) : a ~ b → (a ↔ b) := by
  intro hab
  apply MyEq.subst (P := fun p => a ↔ p) hab
  exact Iff.rfl


/-
-- ============================================================
-- III.6 Exercise 2
-- Exercise 2 — Using the triangle macro (▸)
-- Problem (restated):
--   Find a use for `▸` in a proof of:
--     example (P : Type → Prop) : ∀ x y, x = y → P x → ∃ z, P z
--
-- Idea:
--   Choose `z := y`. From `hx : P x` and `h : x = y`,
--   rewrite/cast `hx` along `h` using the triangle macro:
--     `h ▸ hx : P y`.
-- ============================================================
-/
example (P : Type → Prop) : ∀ x y, x = y → P x → ∃ z, P z := by
  intro x y h hx
  refine ⟨y, ?_⟩
  exact h ▸ hx

/-
-- ============================================================
-- III.6 Exercise 3
-- Exercise 3 — Spin, simp, and rw
-- Problem (restated):
--   For Spin with operation `o` and inverse `x⁻¹`, prove:
--     assoc            : x o (y o z) = (x o y) o z
--     com              : x o y = y o x
--     toggle_op_right  : (x o y)⁻¹ = y o x⁻¹
--     inv_cancel_right : x o x⁻¹ = dn        (as a simp lemma)
--     inv_cancel_left  : x⁻¹ o x = dn        (as a simp lemma)
--
-- Key point:
--   `simp` only works once we either:
--     (1) tell it to unfold `op` via `simp [op]`, or
--     (2) add `[simp]` lemmas for `o` + `⁻¹` like the slides do.
--   We do (2) here so your later `simp` calls actually fire.
-- ============================================================
-/

inductive Spin where | up | dn
open Spin

def Spin.toggle : Spin → Spin
| up => dn
| dn => up

postfix:95 "⁻¹" => Spin.toggle

def op (x y : Spin) : Spin :=
  match x, y with
  | up, dn => dn
  | dn, up => dn
  | _,  _  => up

infix:75 " o " => op

-- --- simp facts (these are the ones your file is missing) ---

@[simp] theorem toggle_up : (up : Spin)⁻¹ = dn := rfl
@[simp] theorem toggle_dn : (dn : Spin)⁻¹ = up := rfl

@[simp] theorem op_up_left {x : Spin} : up o x = x := by
  cases x <;> rfl

@[simp] theorem op_up_right {x : Spin} : x o up = x := by
  cases x <;> rfl

@[simp] theorem op_dn_left {x : Spin} : dn o x = x⁻¹ := by
  cases x <;> rfl

@[simp] theorem op_dn_right {x : Spin} : x o dn = x⁻¹ := by
  cases x <;> rfl

-- --- now the exercise theorems ---

theorem assoc {x y z : Spin} :
  x o (y o z) = (x o y) o z := by
  cases x <;> cases y <;> cases z <;> simp
  -- `simp?` will report it used the op_* simp lemmas above.

theorem com {x y : Spin} :
  x o y = y o x := by
  cases x <;> cases y <;> simp

theorem toggle_op_right {x y : Spin} :
  (x o y)⁻¹ = y o x⁻¹ := by
  cases x <;> cases y <;> simp

@[simp]
theorem inv_cancel_right {x : Spin} :
  x o x⁻¹ = dn := by
  cases x <;> simp

@[simp]
theorem inv_cancel_left {x : Spin} :
  x⁻¹ o x = dn := by
  cases x <;> simp

/-
-- ============================================================
-- III.6 Exercise 4
-- Exercise 4 — Induction on Nat (sum of squares)
-- Problem (restated):
--   Define
--     T : Nat → Nat
--     T 0       = 0
--     T (n+1)   = (n+1)^2 + T n
--   and prove (by induction):
--     ∀ n : Nat, 6 * T n = n * (n+1) * (2*n + 1).
--
-- Strategy:
--   Use `induction n with`.
--   - Base case: `simp [T]`.
--   - Step case: `simp [T, ih]` reduces using the recursive definition,
--     then finish the resulting arithmetic goal with `nlinarith`.
-- ============================================================
-/

def T (n : Nat) : Nat :=
  match n with
  | Nat.zero    => 0
  | Nat.succ x  => n*n + T x

example (n : Nat) : 6 * (T n) = n * (n+1) * (2*n+1) := by
  induction n with
  | zero =>
      simp [T]
  | succ k ih =>
      -- After simp, the goal becomes a polynomial identity in Nat.
      -- `nlinarith` handles the nonlinear arithmetic.
      simp [T]
      nlinarith

/-
-- ============================================================
-- III.6 Exercise 5
-- Exercise 5 — Dyadic inequalities using noConfusion
-- Problem (restated):
--   For Dyadic, show:
--     (1) example (x : Dyadic) : zero ≠ add_one x
--     (2) example :
--           add_one zero ≠ half (add_one (add_one zero))
--   using noConfusion.
-- ============================================================
-/

namespace Temp

inductive Dyadic where
  | zero
  | add_one : Dyadic → Dyadic
  | half : Dyadic → Dyadic
  | neg : Dyadic → Dyadic

def double : Dyadic → Dyadic
  | .zero        => .zero
  | .add_one x   => .add_one (.add_one (double x))
  | .half x      => x
  | .neg x       => .neg (double x)

example (x : Dyadic) :
  Dyadic.zero ≠ Dyadic.add_one x := by
  intro h
  exact Dyadic.noConfusion h

example :
  Dyadic.add_one Dyadic.zero
  ≠ Dyadic.half (Dyadic.add_one (Dyadic.add_one Dyadic.zero)) := by
  intro h
  exact Dyadic.noConfusion h


/-
-- ============================================================
-- III.6 Exercise 6
-- Exercise 6 — Injectivity of add_one
-- Problem (restated):
--   Show:
--     example (x y : Dyadic) :
--       add_one x = add_one y ↔ x = y
-- ============================================================
-/

example (x y : Dyadic) :
  Dyadic.add_one x = Dyadic.add_one y ↔ x = y := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    rfl


/-
-- ============================================================
-- III.6 Exercise 7
-- Exercise 7 — Alternative simp theorems for shift
-- Problem (restated):
--   Instead of using shift_inv_left and shift_inv_right,
--   prove and register as simp:
--     (1) shift_zero : shift 0 = id
--     (2) shift_add  : shift k ∘ shift j = shift (j+k)
--   and show that Bijective (shift k) still holds.
-- ============================================================
-/

def shift (k x : ℤ) : ℤ := x + k


@[simp]
theorem shift_zero : shift 0 = id := by
  funext x
  simp [shift]

@[simp]
theorem shift_add {j k : ℤ} :
  shift k ∘ shift j = shift (j + k) := by
  funext x
  simp [shift, add_assoc]

open Function

example {k : ℤ} : Bijective (shift k) := by
  rw [bijective_iff_has_inverse]
  refine ⟨shift (-k), ?_, ?_⟩
  · -- Left inverse
    -- goal: LeftInverse (shift (-k)) (shift k)
    intro x
    have h : shift (-k) ∘ shift k = id := by
      calc
        shift (-k) ∘ shift k
            = shift (k + (-k)) := by simp [shift_add]
        _ = shift 0 := by simp
        _ = id := by simp [shift_zero]
    simpa [Function.comp] using congrArg (fun f => f x) h
  · -- Right inverse
    intro x
    have h : shift k ∘ shift (-k) = id := by
      calc
        shift k ∘ shift (-k)
            = shift ((-k) + k) := by simp [shift_add]
        _ = shift 0 := by simp
        _ = id := by simp [shift_zero]
    simpa [Function.comp] using congrArg (fun f => f x) h


/-
-- ============================================================
-- III.6 Exercise 8
-- Exercise 8 — For Dyadic show double ∘ half = id
-- Problem (restated):
--   Using the Dyadic type defined earlier, prove:
--     double ∘ half = id
-- ============================================================
-/

example : Temp.double ∘ (fun x => Dyadic.half x) = id := by
  funext x
  cases x <;> rfl

end Temp

/-
============================================================
III.6 Exercise 9
Exercise 9 — Spin ≃ Bool
Problem (restated):
  Define an equivalence between Spin and Bool.
============================================================
-/

def spin_bool_equiv : Spin ≃ Bool :=
{ toFun := fun s =>
    match s with
    | .up => true
    | .dn => false,
  invFun := fun b =>
    match b with
    | true  => Spin.up
    | false => Spin.dn,
  left_inv := by
    intro s
    cases s <;> rfl,
  right_inv := by
    intro b
    cases b <;> rfl }


/-
============================================================
III.6 Exercise 10 (Optional)
Exercise 10 - Define the natural equivalence K1 ≃ K2

Two coordinate systems for “complex numbers”:

structure K1 where
  re : ℝ
  im : ℝ

structure K2 where
  a : ℝ
  θ : ℝ
  pa : 0 ≤ a
  pθ : 0 ≤ θ ∧ θ < 2 * Real.pi
  h : a = 0 → θ = 0

Task:
  Define an equivalence:
    def K_equiv : K1 ≃ K2 := ...

Solution idea (fully constructive, no sorry):
  Use Schroeder–Bernstein by building embeddings both ways:

  • K2 ↪ K1: just forget proof fields and map (a, θ) ↦ (re, im) = (a, θ).
  • K1 ↪ K2: encode re into a := exp re (so a > 0 always),
             encode im into θ := π + arctan im (so θ ∈ [0, 2π)).

  Then apply Function.Embedding.schroederBernstein.
============================================================
-/

structure K1 where
  re : ℝ
  im : ℝ

structure K2 where
  a : ℝ
  θ : ℝ
  pa : 0 ≤ a
  pθ : 0 ≤ θ ∧ θ < 2 * Real.pi
  h : a = 0 → θ = 0

namespace Exercise10

open Real

noncomputable def embedK2ToK1 : K2 ↪ K1 :=
{ toFun := fun k => ⟨k.a, k.θ⟩
  inj' := by
    intro x y hxy
    cases x with
    | mk a1 θ1 pa1 pθ1 h1 =>
      cases y with
      | mk a2 θ2 pa2 pθ2 h2 =>
        have ha : a1 = a2 := by
          exact congrArg K1.re hxy
        have hθ : θ1 = θ2 := by
          exact congrArg K1.im hxy
        cases ha
        cases hθ
        -- remaining fields are proofs (Prop), so proof-irrelevance finishes
        have hpa : pa1 = pa2 := Subsingleton.elim _ _
        have hpθ : pθ1 = pθ2 := Subsingleton.elim _ _
        have hh  : h1  = h2  := Subsingleton.elim _ _
        cases hpa
        cases hpθ
        cases hh
        rfl }

noncomputable def embedK1ToK2 : K1 ↪ K2 :=
{ toFun := fun z =>
    let a : ℝ := Real.exp z.re
    let θ : ℝ := Real.pi + Real.arctan z.im
    have pa : 0 ≤ a := by
      exact le_of_lt (Real.exp_pos z.re)
    have pθ : 0 ≤ θ ∧ θ < 2 * Real.pi := by
      constructor
      · -- 0 ≤ π + arctan(im)
        have hpos : 0 < Real.pi + Real.arctan z.im := by
          have hlow : (-Real.pi / 2) < Real.arctan z.im :=
            Real.neg_pi_div_two_lt_arctan z.im
          linarith [hlow, Real.pi_pos]
        exact le_of_lt hpos
      · -- π + arctan(im) < 2π
        have hhigh : Real.arctan z.im < Real.pi / 2 :=
          Real.arctan_lt_pi_div_two z.im
        linarith [hhigh, Real.pi_pos]
    have h : a = 0 → θ = 0 := by
      intro ha0
      have : False := (Real.exp_ne_zero z.re) ha0
      exact False.elim this
    exact ⟨a, θ, pa, pθ, h⟩
  inj' := by
    intro x y hxy
    cases x with
    | mk xr xi =>
      cases y with
      | mk yr yi =>
        have ha : Real.exp xr = Real.exp yr := by
          exact congrArg K2.a hxy
        have hθ : Real.pi + Real.arctan xi = Real.pi + Real.arctan yi := by
          exact congrArg K2.θ hxy
        have hre : xr = yr := by
          have := congrArg Real.log ha
          simpa [Real.log_exp] using this
        have harct : Real.arctan xi = Real.arctan yi := by
          exact add_left_cancel hθ
        have him : xi = yi := by
          have := congrArg Real.tan harct
          simpa [Real.tan_arctan] using this
        cases hre
        cases him
        rfl }

end Exercise10

noncomputable def K_equiv : K1 ≃ K2 :=
  Function.Embedding.schroederBernstein
    Exercise10.embedK1ToK2
    Exercise10.embedK2ToK1
