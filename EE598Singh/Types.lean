-- ================================================================
-- Exercise 1
-- Problem (restated):
-- What is the type of (Type u ⊕ Type v)?
--
-- ================================================================

universe u v

#check (Type u ⊕ Type v)

-- Lean prints:
--   Type (max (u + 1) (v + 1))
--
-- Why:
--   Type u : Type (u+1)
--   Type v : Type (v+1)
-- and Sum bumps to the max universe of the inputs.


-- ================================================================
-- Exercise 2
-- Problem (restated):
--   def TypeList := List Type
-- Which of these are ok? Why?
--
-- Set up some stand-ins for N and Q so the snippet is self-contained.
-- ================================================================

abbrev N : Type := Nat
abbrev Q : Type := Rat

def TypeList := List Type

-- (1) def A : TypeList := []
def A1 : TypeList := []

-- (2) def A : TypeList := [TypeList]
#check_failure (TypeList : [TypeList])
-- Reason: elements of TypeList must have type `Type` (i.e. Type 0),
-- but TypeList itself lives in a higher universe.

-- (3) def A : TypeList := [N,Q]
def A3 : TypeList := [N, Q]

-- (4) def A : TypeList := [N, N×Type]
#check_failure (TypeList : [N, N × Type])
-- Reason: `Type` is NOT a small type (it is Type 0’s *universe* object),
-- so `N × Type` lives too high to be an element of `List Type`.

-- (5) def A : TypeList := [N,List N]
def A5 : TypeList := [N, List N]

-- (6) def A : TypeList := [N,N×Prop]
def A6 : TypeList := [N, N × Prop]
-- Reason: Prop is Sort 0 and behaves “small enough” here (per slides).

-- (7) def A : TypeList := [N,A]
#check_failure (TypeList : [N, A3])
-- Reason: A3 is a TERM (a list), not a TYPE. TypeList expects types.


-- ================================================================
-- Exercise 3
-- Problem (restated):
-- Change to: def TypeList.{w} := List (Type w)
-- Which of the above work now?
--
-- ================================================================


def TypeList'.{P'} := List (Type P')

-- Refactor each:
def A1' : TypeList'.{0} := []                 -- still works
#check_failure (TypeList'.{0} : [TypeList])  -- still fails, same reason
def A3' : TypeList'.{0} := [N, Q]             -- still works
def A5' : TypeList'.{0} := [N, List N]        -- still works
def A6' : TypeList'.{0} := [N, N × Prop]      -- still works
#check_failure (TypeList'.{0} : [N, A3])      -- still fails (term vs type)

-- The interesting one:
--   TypeList'.{1} = List (Type 1)
-- so every element must be a *type in universe 1* (i.e. something : Type 1).
-- Nat / N lives in Type 0, so it is NOT an element of Type 1 “as-is”.
-- lift it to universe 1.

def A4' : TypeList'.{1} :=
  [ ULift.{1} N
  , (ULift.{1} N) × Type
  ]

-- sanity checks (these should succeed)
#check (ULift.{1} N)        -- : Type 1
#check ((ULift.{1} N) × Type) -- : Type 1
#check A4'

-- Reason:
--   N : Type 0 can be seen as Type 1 (cumulativity)
--   N × Type lives in Type 1
-- so a List (Type 1) can contain both.


-- ================================================================
-- Exercise 4
-- Problem (restated):
-- Why doesn't this type check?
--   def f (n : N) := if n = 0 then Type 0 else Type 1
-- Fix?
--
-- Why the original fails:
--   `if c then t else e` must have ONE fixed return type α.
--   But:
--     Type 0 : Type 1
--     Type 1 : Type 2
--   so the two branches don’t even live in the same universe.
--
-- Fix:
--   `if ... then ... else ...` must return a *single* fixed type.
--   Here the branches are `Type 0` and `Type 1`, which live in different universes:
--     Type 0 : Type 1
--     Type 1 : Type 2
--   So we choose an explicit codomain `Type 2` and make BOTH branches produce an
--   *element* of `Type 2`.
--
--   Key point you were missing:
--     You cannot “coerce” universes. You must *lift* the smaller branch.
--     `ULift` changes the *sort* so that it sits in a higher universe:
--       ULift.{u} : Sort v → Sort (max u v)
--     If we set `u := 2` and apply it to `Type 0` (which is `Sort 1`),
--     we get:
--       ULift.{2} (Type 0) : Sort (max 2 1) = Sort 2 = Type 2
--
--   Why pin `{2}` explicitly?
--     If you leave it implicit, Lean creates a universe metavariable and may get
--     stuck on constraints like `2 = max 1 ?u`.
--
--   Do we get the “forbidden behavior”?
--     We don’t get a universe-breaking coercion. We get a *type-valued result*
--     living in `Type 2`, where the `n=0` branch is a lifted copy of `Type 0`.
-- ================================================================

def f (n : Nat) : Type 2 :=
by
  by_cases h : n = 0
  · -- Type 0 : Type 1, so ULift.{2} (Type 0) : Type (max 2 1) = Type 2
    exact (ULift.{2} (Type 0))
  · -- Type 1 : Type 2 already
    exact (Type 1)

#check f
#reduce f 0
#reduce f 7
