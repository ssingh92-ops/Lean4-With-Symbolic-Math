-- ============================================================
-- Exercise 2
-- Problem (restated):
-- 1) Import the needed Mathlib modules so the file runs.
-- 2) Use #eval to check that Lean can evaluate a simple expression (1+2).
-- 3) Prove the given rational-inequality goal using linarith.
--
-- Textual explanation:
-- - `import Mathlib` loads Mathlib and its common dependencies.
-- - `#eval` evaluates an expression and prints the result in the InfoView.
-- - `linarith` is a tactic that solves goals that are linear combinations of
--   inequalities/equalities (linear arithmetic). Here it derives a contradiction.
-- ============================================================

import Mathlib

#eval 1 + 2
-- Expected output: 3

example (x y z : ℚ)
        (h1 : 2 * x < 3 * y)
        (h2 : -4 * x + 2 * z < 0)
        (h3 : 12 * y - 4 * z < 0) : False := by
  linarith


-- ============================================================
-- Exercise 3
-- Problem (restated):
-- Encode the statement:  ∀ x : ℝ, 0 ≤ x^2
--
-- Textual explanation:
-- - `∀ x : ℝ, ...` means “for all real numbers x, ...”.
-- - `x^2` is x squared.
-- - `0 ≤ x^2` states that a square is always nonnegative.
-- - The assignment says it is fine to just encode the statement.
-- ============================================================

theorem T₁ : ∀ x : ℝ, 0 ≤ x^2 := sorry


-- ============================================================
-- Exercise 4
-- Problem (restated):
-- Use `#check` to determine the types of: (4,5), ℕ × ℕ, and Type.
--
-- Textual explanation:
-- - `(4,5)` has type `Nat × Nat` (a pair of natural numbers).
-- - `ℕ × ℕ` has type `Type` (it is itself a type).
-- - `Type` has type `Type 1` (a higher universe level).
-- ============================================================

#check (4,5)
#check ℕ × ℕ
#check Type


-- ============================================================
-- Exercise 5
-- Problem (restated):
-- Lean provides a tactic called `aesop`. Redo the proof of:
--   (p → q) ∧ (q → r) → (p → r)
-- replacing the proof with the single line `aesop`.
--
-- Textual explanation:
-- - This is “transitivity of implication” packaged through a conjunction:
--   from (p→q) and (q→r), can conclude (p→r).
-- - `aesop` is an automation tactic that can solve many routine logical goals.
-- ============================================================

example (p q r : Prop) : (p → q) ∧ (q → r) → (p → r) := by
  aesop


-- ============================================================
-- Exercise 6
-- Problem (restated):
-- Write a function `square` that squares every number in a list of natural numbers.
-- Use `remove_zeros` as a template. Test code using `#eval`.
--
-- Textual explanation:
-- - This is basic recursion + pattern matching on lists:
--   * if the list is empty, return [].
--   * if the list is x :: Q, return (x^2) :: square Q.
-- - `#eval` confirms it actually computes the expected list.
-- ============================================================

def square (L : List ℕ) : List ℕ :=
  match L with
  | [] => List.nil
  | x :: Q => x^2 :: square Q

#check square
-- Expected: square : List ℕ → List ℕ

#eval square [1,2,3,4,5,20,11]
-- Expected output: [1, 4, 9, 16, 25, 400, 121]


-- ============================================================
-- Exercise 7
-- Problem (restated):
-- Look up `List.find?` and try the two examples of how to use it.
--
-- Textual explanation:
-- - `find?` has type: (p : α → Bool) → List α → Option α
-- - It returns the first element that satisfies the predicate p, wrapped in `some`.
-- - If no element satisfies p, it returns `none`.
-- - In these examples, the predicate is “x < 5” or “x < 1”.
-- ============================================================

#eval ([7, 6, 5, 8, 1, 2, 6] : List Nat).find? (fun x => x < 5)
-- Expected output: some 1

#eval ([7, 6, 5, 8, 1, 2, 6] : List Nat).find? (fun x => x < 1)
-- Expected output: none
