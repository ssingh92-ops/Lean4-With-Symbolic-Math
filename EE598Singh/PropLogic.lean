import Mathlib
import EE598Singh.Basic

/-
-- ============================================================
--  III.1 Exercise 1
-- Exercise 1 — Propositional Logic
-- Problem (restated):
-- For propositions p, q, r, prove the following two implications constructively or explain why not:
--
-- (1)  p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)
-- (2)  (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)
--
-- Answer:
--   (2) cannot, in general, be proven constructively (i.e. without Classical.em / excluded middle).
--   (1) *is* constructively provable.
--
-- Why (1) is constructive:
--   A proof of p ∨ (q ∧ r) comes with data: either hp : p, or hqr : q ∧ r.
--   - If hp : p, then build both (p ∨ q) and (p ∨ r) via ∨-Intro-Left.
--   - If hqr : q ∧ r, then build (p ∨ q) via ∨-Intro-Right using q, and
--     build (p ∨ r) via ∨-Intro-Right using r.
--
-- Why (2) needs excluded middle:
--   From h : (p ∨ q) ∧ (p ∨ r), one has:
--     h.left  : p ∨ q
--     h.right : p ∨ r
--   To prove p ∨ (q ∧ r), a choice is required:
--     - either produce p, or
--     - produce both q and r.
--   If ¬p were known, q can be extracted from (p ∨ q) and r from (p ∨ r), hence q ∧ r.
--   If p were known, finish immediately.
--   The missing ingredient is a case split on p:
--       p ∨ ¬p
--   i.e. excluded middle.
-- ============================================================
-/

-- (2) in ordinary Lean Prop (sanity check; uses classical case split)
example (p q r : Prop) : (p ∨ q) ∧ (p ∨ r) → (p ∨ (q ∧ r)) := by
  intro h1
  classical
  by_cases hp : p
  · exact Or.inl hp
  · -- hp : ¬ p
    have hq : q := by
      cases h1.1 with
      | inl hp' => exact False.elim (hp hp')
      | inr hq  => exact hq
    have hr : r := by
      cases h1.2 with
      | inl hp' => exact False.elim (hp hp')
      | inr hr  => exact hr
    exact Or.inr ⟨hq, hr⟩

/-
-- ============================================================
--  III.1 Exercise 2
-- Exercise 2:
-- Problem: Prove by hand  ⊢ (p → q) → p → q.
--
-- Goal: ∅ ⊢ (p → q) → p → q
--
-- 1) Apply →-Intro:
--    {p → q} ⊢ p → q
--
-- 2) Apply →-Intro:
--    {p → q, p} ⊢ q
--
-- 3) Apply →-Elim (modus ponens) using:
--    - {p → q, p} ⊢ p → q   (Axiom)
--    - {p → q, p} ⊢ p       (Axiom)
--    Conclude {p → q, p} ⊢ q.
-- ============================================================
-/

-- Sanity check in Lean:
example (p q : Prop) : (p → q) → p → q := by
  intro hpq hp
  exact hpq hp

/-
-- ============================================================
-- III.1 Exercise 3
-- Exercise 3 — Propositional Logic (∧, ∨)
-- Problem (restated):
--   Prove ⊢ p ∧ q → p ∨ q.
--
-- By-hand proof tree (rule-by-rule, matching the slide deck):
--
-- Goal: ⊢ p ∧ q → p ∨ q
--
-- (1) →-Intro:
--     {p ∧ q} ⊢ p ∨ q
--
-- (2) ∧-Elim-Left:
--     {p ∧ q} ⊢ p
--
-- (3) ∨-Intro-Left:
--     {p ∧ q} ⊢ p ∨ q
--
-- Therefore: ⊢ p ∧ q → p ∨ q.
-- ============================================================
-/

-- Sanity check in Lean:
example (p q : Prop) : p ∧ q → p ∨ q := by
  intro h
  exact Or.inl h.left

/-
-- ============================================================
-- III.1 Exercise 4
-- Exercise 4 — Propositional Logic
-- Problem (restated):
--   Prove ⊢ (¬¬p ↔ p).
--   One direction requires classical logic.
--   For that direction: formally state LEM as an inference rule and use it.
--
-- ------------------------------------------------------------
-- Conventions (as in slide deck):
--   ¬p  := p → ⊥
--   ¬¬p := (¬p → ⊥)
--
-- False-Elim (Ex Falso):
--        Γ ⊢ ⊥
--      ---------  False-Elim
--        Γ ⊢ φ
--
-- Law of Excluded Middle (LEM) as an inference rule:
--     (no premises)
--     ----------------  LEM
--        Γ ⊢ p ∨ ¬p
--
-- ------------------------------------------------------------
-- Proof-tree plan:
--
-- Goal: ⊢ (¬¬p ↔ p)
-- Prove both directions, then ↔-Intro.
--
-- Direction A (constructive): ⊢ p → ¬¬p
--   →-Intro: {p} ⊢ ¬¬p
--   expand ¬¬p: {p} ⊢ (¬p → ⊥)
--   →-Intro: {p, ¬p} ⊢ ⊥
--   →-Elim using ¬p : (p → ⊥) and p : p (both by Axiom).
--
-- Direction B (classical): ⊢ ¬¬p → p
--   →-Intro: {¬¬p} ⊢ p
--   use LEM: {¬¬p} ⊢ (p ∨ ¬p)
--   ∨-Elim with result ρ := p:
--     (i)  {¬¬p} ⊢ (p → p)        by →-Intro then Axiom
--     (ii) {¬¬p} ⊢ (¬p → p)       by →-Intro, then derive ⊥ via →-Elim
--          using ¬¬p : (¬p → ⊥) and ¬p (Axiom), then False-Elim to get p.
--
-- Combine by ↔-Intro.
-- ============================================================
-/

-- Sanity check in ordinary Lean Prop (separate from proof-tree system)
example (p : Prop) : (¬¬p ↔ p) := by
  constructor
  · intro hnnp
    classical
    by_cases hp : p
    · exact hp
    · exfalso
      exact hnnp hp
  · intro hp hnp
    exact hnp hp

/-
-- ============================================================
-- III.1 Exercise 5
-- Exercise 5 — Or distributes over And (both directions)
-- Problem (restated):
--   Prove both:
--   (1) ⊢ p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)
--   (2) ⊢ (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)
--       using excluded middle where needed.
-- ============================================================
-/

-- (1) constructive
example (p q r : Prop) : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) := by
  intro h
  cases h with
  | inl hp =>
      exact And.intro (Or.inl hp) (Or.inl hp)
  | inr hqr =>
      exact And.intro (Or.inr hqr.left) (Or.inr hqr.right)

-- (2) classical (needs excluded middle on p)
example (p q r : Prop) : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) := by
  intro h
  classical
  by_cases hp : p
  · exact Or.inl hp
  · have hq : q := by
      cases h.1 with
      | inl hp' => exact False.elim (hp hp')
      | inr hq  => exact hq
    have hr : r := by
      cases h.2 with
      | inl hp' => exact False.elim (hp hp')
      | inr hr  => exact hr
    exact Or.inr ⟨hq, hr⟩

/-
-- ============================================================
-- III.2 Exercise 1g
-- Exercise 1 — Lambda Calculus Proofs
--
-- Problem:
-- Prove the following using only lambda expressions
-- (and possibly `nomatch`).
--
-- Given:
--   variable (P Q : Prop)
--
--   (1) P → P → P → P
--   (2) (P → Q) → (¬Q → ¬P)
--   (3) ¬P → (P → Q)
--   (4) (∀ x, x > 0) → (∀ y, y > 0)
--
-- Notes:
-- - These are proofs-as-programs via Curry–Howard.
-- - Implication corresponds to function types.
-- - Negation ¬P is defined as P → False.
-- ============================================================
-/

variable (P Q : Prop)

-- (1) P → P → P → P
-- Keep the first argument and ignore the rest.
example : P → P → P → P :=
  fun p _ _ => p

-- (2) (P → Q) → (¬Q → ¬P)
-- Proof by contrapositive, encoded as function composition.
example : (P → Q) → (¬Q → ¬P) :=
  fun hpq hnotq hp => hnotq (hpq hp)

-- (3) ¬P → (P → Q)
-- From a contradiction, anything follows (ex falso).
example : ¬P → (P → Q) :=
  fun hnp hp => nomatch (hnp hp)

-- (4) (∀ x, x > 0) → (∀ y, y > 0)
-- Universally quantified propositions are functions.
example : (∀ x, x > 0) → (∀ y, y > 0) :=
  fun h y => h y
