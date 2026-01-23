/-
HW II.5 — EE598

Instructions (from slide deck):
- Put solutions in HW_II_5.lean in the same directory as Basic.lean.
- Restate each problem.
- Textual answers should be written as comments.
- Lean code should produce no errors (sorry is allowed for partial credit).
-/

import mathlib

-- ================================================================
-- Exercise 1 — Type Inference
-- Problem restated:
-- Show that the expression `fun x => fun f => f x` has type `A → (A → B) → B`
-- for some types `A` and `B`, using a derivation tree (VAR / ABST / APPL).
-- ================================================================
/-
Derivation tree (informal, rule-by-rule):

Let Γ₀ := ·
Let Γ₁ := (x : A)
Let Γ₂ := (x : A, f : A → B)

1) By VAR on f:
   Γ₂ ⊢ f : A → B

2) By VAR on x:
   Γ₂ ⊢ x : A

3) By APPL on (1) and (2):
   Γ₂ ⊢ f x : B

4) By ABST (abstract f):
   Γ₁ ⊢ (fun f : A → B => f x) : (A → B) → B

5) By ABST (abstract x):
   Γ₀ ⊢ (fun x : A => fun f : A → B => f x) : A → (A → B) → B
-/

-- Lean version
def ex1 {A B : Type} : A → (A → B) → B :=
  fun x : A => fun f : A → B => f x

#check ex1
-- ex1 : {A B : Type} → A → (A → B) → B




-- ===============================================================
-- Exercise 2 — Inhabitation (Vec)
-- Problem restated:
-- Given
--
-- inductive Vec (α : Type) : Nat → Type where
--  | nil  : Vec α 0
--  | cons {n} : α → Vec α n → Vec α (n + 1)
--
-- Construct terms (definitions) to replace `sorry` in:
--
--  def g1 : N → Vec N 0 := sorry
--  def g2 : Σ n, Vec N n := sorry
--  def g3 : Π f : N → N, Σ n, Vec N (f n) := sorry
--  def g4 : Σ A, Π B, Vec A B := sorry
-- ===============================================================

-- A helper: a vector of zeros of any length.
universe u'

inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

namespace Vec

def zeros : (k : Nat) → Vec Nat k
| 0        => Vec.nil
| Nat.succ k => Vec.cons 0 (zeros k)

-- g1 : N → Vec N 0
-- Any Vec _ 0 is definitionally `nil`, so we ignore the input.
def g1 : Nat → Vec Nat 0 :=
  fun _ => Vec.nil

-- g2 : Σ n, Vec N n
-- Pick n = 0 and the empty vector.
def g2 : Sigma (fun n : Nat => Vec Nat n) :=
  ⟨0, Vec.nil⟩

-- g3 : Π f : N → N, Σ n, Vec N (f n)
-- For any f, pick n = 0 and build a vector of length (f 0) filled with zeros.
def g3 : (f : Nat → Nat) → Sigma (fun n : Nat => Vec Nat (f n)) := by
  intro f
  exact ⟨0, zeros (f 0)⟩

/-
If your goal literally is:
  def g3 : Π f : N → N, Σ n, Vec N (f n) := ...
then use:
  def g3 : (Nat → Nat) → Sigma (fun n : Nat => Vec Nat (f n)) := ...
in a context where `f` is in scope.

Most directly (in that exact shape):
-/
def g3' : (f : Nat → Nat) → Sigma (fun n : Nat => Vec Nat (f n)) :=
  fun f => ⟨0, zeros (f 0)⟩

-- g4 : Σ A, Π B, Vec A B
-- Choose A = Nat, and for each length B : Nat return `zeros B`.
def g4 : Sigma (fun A : Type u => (B : Nat) → Vec A B) := by
  refine ⟨ULift Nat, ?_⟩
  intro B
  induction B with
  | zero =>
      exact Vec.nil
  | succ k hk =>
      exact Vec.cons (ULift.up 0) hk

end Vec
