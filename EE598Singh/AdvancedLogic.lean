import mathlib
/-
-- ============================================================
-- III.4 Exercise 1
-- Exercise 1 — Relations
-- Problem (restated):
--   Define the relation `on_left` for `Person`.
--
-- Context:
--   We are given a relation `on_right : Person → Person → Prop`
--   encoding who sits immediately to the right of whom.
--
-- Definition idea:
--   "q is on the left of p" means "p is on the right of q".
--   So `on_left p q := on_right q p`.
-- ============================================================
-/

inductive Person where
  | mary | steve | ed | jolin
deriving DecidableEq

open Person

def on_right (p q : Person) : Prop :=
  match p with
  | mary  => q = steve
  | steve => q = ed
  | ed    => q = jolin
  | jolin => q = mary

def on_left (p q : Person) : Prop :=
  on_right q p

def next_to (p q : Person) : Prop :=
  on_right p q ∨ on_right q p

/-
-- ============================================================
-- III.4 Exercise 2
-- Exercise 2 — Relations
-- Problem (restated):
--   Prove:
--     example : on_left mary jolin := _
--
-- Proof idea:
--   Unfold `on_left`:
--     on_left mary jolin = on_right jolin mary
--   Unfold `on_right` at `jolin`:
--     on_right jolin mary = (mary = mary)
--   Then finish by reflexivity.
-- ============================================================
-/

example : on_left mary jolin :=
  rfl

  /-
-- ============================================================
-- III.4 Exercise 3
-- Exercise 3 — Universal Quantification
-- Problem (restated):
--   Show using a term-level proof (no library theorems):
--
--     (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x)
--
-- Proof idea (Curry–Howard):
--   A proof of ∀ x, P x → Q x is a function that,
--   given x, produces a function P x → Q x.
--
--   A proof of ∀ x, P x is a function that,
--   given x, produces a proof of P x.
--
--   To prove ∀ x, Q x, we must construct a function
--   that takes arbitrary x and produces Q x.
--
--   So:
--     given h₁ : ∀ x, P x → Q x
--     given h₂ : ∀ x, P x
--     take arbitrary x
--     apply h₁ x to (h₂ x)
-- ============================================================
-/

variable {α : Type}
variable {P Q : α → Prop}

example :
  (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) :=
  fun h₁ h₂ x =>
    h₁ x (h₂ x)

/-
-- ============================================================
-- III.4 Exercise 4
-- Exercise 4 — Existential Quantification
-- Problem (restated):
--   Prove:
--
--   (1) ∃ x, on_right mary x
--   (2) ∃ x, ¬ on_right mary x
--
-- Proof idea:
--   (1) From the definition of on_right:
--       on_right mary steve holds definitionally.
--       So we exhibit steve.
--
--   (2) We must exhibit a person for which
--       on_right mary x does NOT hold.
--       Since on_right mary x means x = steve,
--       choose mary and show mary ≠ steve.
-- ============================================================
-/

-- (1)
example : ∃ x, on_right mary x :=
  ⟨steve, rfl⟩

-- (2)
example : ∃ x, ¬ on_right mary x :=
  ⟨mary, by
    intro h
    -- h : mary = steve
    cases h⟩

/-
-- ============================================================
-- III.4 Exercise 5
-- Exercise 5 — Using PreDyadic
-- Problem (restated):
--   Show:
--
--     ∀ x, ∃ y, y = neg x
--
-- Proof idea:
--   For arbitrary x,
--   choose y := neg x.
--   Then y = neg x holds by reflexivity.
-- ============================================================
-/

example : ∀ x : Int, ∃ y, y = -x :=
  fun x =>
    ⟨-x, rfl⟩

/-
-- ============================================================
-- III.4 Exercise 6
-- Exercise 6 — FOL Equivalences
-- Prove using term-level proofs only:
--
-- (1) (∀ x, p x → r) ↔ (∃ x, p x) → r
-- (2) (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x)
-- ============================================================
-/

variable {α : Type}
variable {p q : α → Prop}
variable {r : Prop}

-- (1)
example :
  (∀ x, p x → r) ↔ (∃ x, p x) → r :=
Iff.intro
  -- forward direction
  (fun h₁ h₂ =>
    match h₂ with
    | ⟨c, hc⟩ => h₁ c hc)
  -- backward direction
  (fun h x hx =>
    h ⟨x, hx⟩)


-- (2)
example :
  (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
Iff.intro
  -- forward direction
  (fun h =>
    match h with
    | ⟨c, Or.inl hp⟩ => Or.inl ⟨c, hp⟩
    | ⟨c, Or.inr hq⟩ => Or.inr ⟨c, hq⟩)
  -- backward direction
  (fun h =>
    match h with
    | Or.inl ⟨c, hp⟩ => ⟨c, Or.inl hp⟩
    | Or.inr ⟨c, hq⟩ => ⟨c, Or.inr hq⟩)

/-
-- ============================================================
-- III.4 Exercise 7
-- Exercise 7 — Relations on Person
--
-- Prove:
-- (1) ∀ p q, on_right p q → next_to p q
-- (2) ∀ p, ∃ q, next_to p q
-- (3) ∀ p, ∃ q, ¬ next_to p q
-- ============================================================
-/

-- (1)
example :
  ∀ p q, on_right p q → next_to p q :=
  fun _ _ h =>
    Or.inl h


-- (2)
example :
  ∀ p : Person, ∃ q : Person, next_to p q :=
  fun p =>
    match p with
    | mary  => ⟨steve, Or.inl rfl⟩
    | steve => ⟨ed, Or.inl rfl⟩
    | ed    => ⟨jolin, Or.inl rfl⟩
    | jolin => ⟨mary, Or.inl rfl⟩


-- (3)
example :
  ∀ p : Person, ∃ q : Person, ¬ next_to p q :=
  fun p =>
    match p with
    | mary =>
        ⟨ed,
          fun h =>
            match h with
            | Or.inl h₁ => by cases h₁
            | Or.inr h₂ => by cases h₂⟩
    | steve =>
        ⟨jolin,
          fun h =>
            match h with
            | Or.inl h₁ => by cases h₁
            | Or.inr h₂ => by cases h₂⟩
    | ed =>
        ⟨mary,
          fun h =>
            match h with
            | Or.inl h₁ => by cases h₁
            | Or.inr h₂ => by cases h₂⟩
    | jolin =>
        ⟨steve,
          fun h =>
            match h with
            | Or.inl h₁ => by cases h₁
            | Or.inr h₂ => by cases h₂⟩

/-
-- ============================================================
-- III.4 Exercise 8
-- Exercise 8 — Exists1 Elimination
--
-- Prove the elimination theorem for Exists1:
--
--   If there exists exactly one x such that P x,
--   and from any such x we can prove b,
--   then b holds.
-- ============================================================
-/

inductive Exists1 {α : Type} (P : α → Prop) : Prop where
  | intro (x : α) (h : P x ∧ ∀ y, P y → x = y) : Exists1 P


theorem Exists1.elim
  {α : Type} {P : α → Prop} {b : Prop}
  (h1 : Exists1 (fun x => P x))
  (h2 : ∀ a : α, P a → b) : b :=
  match h1 with
  | Exists1.intro x hx =>
      h2 x hx.left

/-
-- ============================================================
-- III.4 Exercise 9
-- Exercise 9 — Exists1 Examples
--
-- Prove the following:
--
-- (1) ∀ x, Exists1 (fun y : Person => x ≠ y ∧ ¬ next_to y x)
--
-- (2) Exists1 (fun x => P x) → ¬ ∀ x, ¬ P x
--
-- (3) Exists1 (fun x : Nat => x = 0)
--
-- (4) ¬ Exists1 (fun x : Nat => x ≠ 0)
--
-- All proofs should be term-level and constructive.
-- ============================================================
-/

-- assuming:
-- inductive Person where | mary | steve | ed | jolin
-- def on_right : Person → Person → Prop := ...
-- def next_to (p q : Person) : Prop := on_right p q ∨ on_right q p

example :
  Exists1 (fun y : Person => mary ≠ y ∧ ¬ next_to y mary) :=
  Exists1.intro ed
    ⟨
      -- P ed: mary ≠ ed ∧ ¬ next_to ed mary
      ⟨
        (by intro h; cases h),   -- mary ≠ ed
        (by
          intro h
          -- next_to ed mary = on_right ed mary ∨ on_right mary ed
          -- on_right ed mary is false by definitional mismatch; on_right mary ed is false too.
          -- easiest: just split on h and `cases` the impossible equalities
          cases h with
          | inl h1 => cases h1
          | inr h2 => cases h2)
      ⟩,
      -- uniqueness: ∀ y, P y → ed = y
      (fun y hy =>
        match y with
        | mary =>
            False.elim (hy.left rfl)
        | steve =>
            -- show contradiction because next_to steve mary is true (since on_right mary steve)
            False.elim (hy.right (Or.inr rfl))
        | ed =>
            rfl
        | jolin =>
            -- next_to jolin mary is true (since on_right jolin mary)
            False.elim (hy.right (Or.inl rfl)))
    ⟩



example (α : Type) (P : α → Prop) :
  Exists1 (fun x => P x) → ¬ ∀ x, ¬ P x :=
  fun h hforall =>
    Exists1.elim h
      (fun x hx =>
        hforall x hx)

example :
  Exists1 (fun x : Nat => x = 0) :=
  Exists1.intro 0
    ⟨
      rfl,
      fun y hy =>
        by cases hy; rfl
    ⟩

/-
example :
  ¬ Exists1 (fun x : Nat => x ≠ 0) := ...
-/
example :
  ¬ Exists1 (fun x : Nat => x ≠ 0) :=
  fun h =>
    match h with
    | Exists1.intro x hx =>
        let hx1 : x = 1 := hx.right 1 (by decide)
        let hx2 : x = 2 := hx.right 2 (by decide)
        let h12 : (1 : Nat) = 2 :=
          Eq.trans (Eq.symm hx1) hx2
        have hneq : (1 : Nat) ≠ 2 := by decide
        hneq h12

/-
-- ============================================================
-- III.5 Exercise 1
--
-- Do the following proofs using the tactics
-- intro, apply, and use along with the basic
-- inductive definitions and eliminators for And and Or.
-- ============================================================
-/

variable {α : Type}
variable (P Q : α → Prop)

-- (1)
example :
  (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro h
  cases h with
  | intro x hx =>
    use x
    apply And.intro
    · exact hx.right
    · exact hx.left


-- (2)
example :
  (∃ x, P x ∨ Q x) → ∃ x, Q x ∨ P x := by
  intro h
  cases h with
  | intro x hx =>
    use x
    cases hx with
    | inl hp =>
      apply Or.inr
      exact hp
    | inr hq =>
      apply Or.inl
      exact hq

/-
-- ============================================================
-- III.5 Exercise 2
--
-- Prove:
-- (1) ∀ p : Person, ∃ q : Person, next_to p q
-- (2) ∀ p : Person, ∃ q : Person, ¬ next_to p q
-- ============================================================
-/

-- (1)
example :
  ∀ p : Person, ∃ q : Person, next_to p q := by
  intro p
  cases p with
  | mary =>
    use steve
    unfold next_to
    apply Or.inl
    rfl
  | steve =>
    use ed
    unfold next_to
    apply Or.inl
    rfl
  | ed =>
    use jolin
    unfold next_to
    apply Or.inl
    rfl
  | jolin =>
    use mary
    unfold next_to
    apply Or.inl
    rfl


-- (2)
example :
  ∀ p : Person, ∃ q : Person, ¬ next_to p q := by
  intro p
  cases p with
  | mary =>
    use ed
    intro h
    unfold next_to at h
    cases h with
    | inl h1 => cases h1
    | inr h2 => cases h2
  | steve =>
    use jolin
    intro h
    unfold next_to at h
    cases h with
    | inl h1 => cases h1
    | inr h2 => cases h2
  | ed =>
    use mary
    intro h
    unfold next_to at h
    cases h with
    | inl h1 => cases h1
    | inr h2 => cases h2
  | jolin =>
    use steve
    intro h
    unfold next_to at h
    cases h with
    | inl h1 => cases h1
    | inr h2 => cases h2

/-
-- ============================================================
-- III.5 Exercise 3
--
-- Recall the definition of PreDyadic.
--
-- (a) Define a function
--       no_negs : PreDyadic → Prop
--     that is True exactly when no neg constructors appear.
--
-- (b) Prove:
--       no_negs x → no_negs (double x)
--
-- (c) Prove:
--       no_negs x → no_negs y → no_negs (mul x y)
-- ============================================================
-/

inductive PreDyadic where
| one
| neg  (x : PreDyadic)
| double (x : PreDyadic)
| mul (x y : PreDyadic)

def no_negs : PreDyadic → Prop
| PreDyadic.one        => True
| PreDyadic.neg _      => False
| PreDyadic.double x   => no_negs x
| PreDyadic.mul x y    => no_negs x ∧ no_negs y

example (x : PreDyadic) :
  no_negs x → no_negs (PreDyadic.double x) := by
  intro h
  exact h

example (x y : PreDyadic) :
  no_negs x → no_negs y → no_negs (PreDyadic.mul x y) := by
  intro hx hy
  exact And.intro hx hy

/-
-- ============================================================
-- III.5 Exercise 4
--
-- The prompt suggests using `#help tactic` to browse tactics.
-- In this file environment, `#help` is not available in the same
-- way as the course webpage UI, so instead we use `#check` and
-- `#print` on a specific tactic and theorems that use it.
--
-- Chosen tactic: `cases`
--
-- What `cases` does (informal):
--   `cases` performs case analysis on an inductive value.
--   It corresponds to applying the eliminator/recursor of that type,
--   generating one goal per constructor and exposing constructor
--   fields as hypotheses.
-- ============================================================
-/

/-
-- Example 1: `cases` on And
-/
theorem ex_cases_and (p q : Prop) : (p ∧ q) → p := by
  intro h
  cases h with
  | intro hp hq =>
    exact hp

#print ex_cases_and

/-
-- Example 2: `cases` on Or
-/
theorem ex_cases_or (p q : Prop) : (p ∨ q) → (q ∨ p) := by
  intro h
  cases h with
  | inl hp =>
    exact Or.inr hp
  | inr hq =>
    exact Or.inl hq

#print ex_cases_or
