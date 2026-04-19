-- ================================================================
-- Exercise 1
-- Show that (→) is not associative by giving terms with types:
--   (1) Type → (Type → Type)
--   (2) (Type → Type) → Type
--
-- Key idea:
--   A → B → C = A → (B → C) (right-associative), so parentheses matter.
-- ================================================================

-- (1) Type → (Type → Type)
-- Given A : Type, return a function (B : Type) ↦ A.
def ex1_right : Type → (Type → Type) :=
  fun (A : Type) => fun (_ : Type) => A

#check ex1_right
-- ex1_right : Type → Type → Type   (Lean prints right-associated)

-- (2) (Type → Type) → Type
-- Given g : Type → Type, produce a Type by applying g to a concrete Type (Nat).
def ex1_left : (Type → Type) → Type :=
  fun (g : Type → Type) => g Nat

#check ex1_left

-- ================================================================
-- Exercise 2
-- String.append : String → String → String
-- Define prepend_label that prepends "STRING: " to its argument
-- by combining with String.append. Test it.
-- ================================================================

def prepend_label : String → String :=
  String.append "STRING: "

#check prepend_label
-- prepend_label : String → String

#eval prepend_label "hello"
#eval prepend_label ""


-- ================================================================
-- Exercise 3
-- Create a context/goal state matching:
--   { a : A, b : B, f : A → B } ⊢ f a : B
-- ================================================================

variable (A B : Type) (a : A) (b : B) (f : A → B)

#check f a
-- ⊢ f a : B

-- Or as an explicit goal:
example (A B : Type) (a : A) (f : A → B) : B :=
  f a

-- ================================================================
-- Exercise 4
-- Goal:
--   Given x : A, build a term M : A such that
--     (1) Size(M) = 5   (per the slide’s inductive Size definition)
--     (2) M β-reduces to x
--
-- Construction idea (hit Size = 5 on the nose):
--   Take one application node (adds 1),
--   apply a constant-function abstraction (adds 1 + Size(body)),
--   to an identity abstraction (adds 1 + Size(var)).
--
--   M := (fun (y : A → A) => x) (fun (z : A) => z)
--
-- Size check (using the slide rules):
--   Size(x) = 1
--   Size(fun (y : A → A) => x) = 1 + Size(x) = 2
--   Size(fun (z : A) => z)     = 1 + Size(z) = 2
--   Size(M) = 1 + 2 + 2 = 5
--
-- β-reduction:
--   (fun (y : A → A) => x) (fun (z : A) => z)  --β-->  x
--   since x does not depend on y.
-- ================================================================

variable (A : Type) (x : A)

def M : A :=
  (fun (_ : A → A) => x) (fun (z : A) => z)

#check M      -- M : A
#reduce M     -- reduces to x

-- ================================================================
-- Problem 5 (Church numerals):
-- define `double` and test it.
-- Goal (from the slide):
-- Define a lambda abstraction, called `double`, that takes a Church numeral
-- and doubles it. Evaluate it on a few examples.
-- ================================================================

def α := Type

def c0 := fun (_ : α → α) => fun (x : α) => x
def c1 := fun (f : α → α) => fun (x : α) => f x
def c2 := fun (f : α → α) => fun (x : α) => f (f x)
def c3 := fun (f : α → α) => fun (x : α) => f (f (f x))

-- The shared type of Church numerals
def N := (α → α) → α → α

/-
------------------------------------------------------------
Solution
Idea: a numeral `n` is "do f n times".
So "double n" should do f (2n) times.
A clean way: do n times, then do n times again.
------------------------------------------------------------
-/
def double : N → N :=
  fun (n : N) =>
    fun (f : α → α) =>
      fun (x : α) =>
        n f (n f x)

/-
------------------------------------------------------------
Quick evaluations
These should β-reduce to the expected λ-terms:
  double c0 = c0
  double c1 = c2
  double c2 = (apply f 4 times)
  double c3 = (apply f 6 times)
------------------------------------------------------------
-/
#reduce (types := true) (double c0)
#reduce (types := true) (double c1)
#reduce (types := true) (double c2)
#reduce (types := true) (double c3)

-- =========================================================
-- Exercise 6
-- "Rewrite them by giving the variables types. Use #check."
-- =========================================================

-- (1) fun x y => x y
#check (fun (A B : Type) (x : A → B) (y : A) => x y)

-- (2) fun x y z => x y z
#check (fun (A B C : Type) (x : A → B → C) (y : A) (z : B) => x y z)

-- (3) fun x y => y (y (y x))
#check (fun (A : Type) (x : A) (y : A → A) => y (y (y x)))

-- (4) fun x y z => (y x) z
#check (fun (A B C : Type) (x : A) (y : A → B → C) (z : B) => (y x) z)

-- ============================================================
-- Exercise 7 (Church Encodings): Church Pairs
-- Problem (restated):
-- (Church Encodings): Church Pairs

-- What I did:
-- - Implemented the Church encoding of pairs (2-tuples) in Lean.
-- - Defined PAIR, FST, SND exactly in the Church style:
--     PAIR x y := (fun z => z x y)
--     FST p   := p (fun x y => x)
--     SND p   := p (fun x y => y)
-- - Tested by reducing on a few concrete examples (Nat and String).
-- Source idea: Church pairs section on the Church encoding page.
-- ============================================================

-- Church-encoded pair type (polymorphic "result type" C)
def CP (A B : Type) : Type 1 := (C : Type) → (A → B → C) → C

-- Constructor: package a : A and b : B
def PAIR {A B : Type} (a : A) (b : B) : CP A B :=
  fun _C f => f a b

-- First projection
def FST {A B : Type} (p : CP A B) : A :=
  p A (fun a _b => a)

-- Second projection
def SND {A B : Type} (p : CP A B) : B :=
  p B (fun _a b => b)

/- ---------------------------------------------------------
   Quick type checks
--------------------------------------------------------- -/
#check CP
#check @PAIR
#check @FST
#check @SND

/- ---------------------------------------------------------
   Tests (evaluation)
--------------------------------------------------------- -/
#reduce (types := true) FST (PAIR (A := Nat) (B := Nat) 3 5)
#reduce (types := true) SND (PAIR (A := Nat) (B := Nat) 3 5)

#reduce (types := true) FST (PAIR (A := String) (B := Nat) "hello" 42)
#reduce (types := true) SND (PAIR (A := String) (B := Nat) "hello" 42)

/- =========================
   Short Writeup
   =========================
Implemented the Church encoding of pairs: a pair is represented as a function
that, given any result type C and a "consumer" f : A → B → C, returns f applied
to the two stored components. Then cfst/csnd retrieve components by choosing
C = A (or C = B) and supplying the appropriate selector function.
-/
