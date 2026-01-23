/-
HW II.4 — EE598

Instructions (from slide deck):
- Put solutions in HW_II_4.lean in the same directory as Basic.lean.
- Restate each problem.
- Textual answers should be written as comments.
- Lean code should produce no errors (sorry is allowed for partial credit).
-/

import mathlib


-- ================================================================
-- Exercise 1
-- Problem (restated):
-- Define a simple pair type `Pair` with two components of possibly different types.
-- ================================================================

universe u v

/-- A simple pair type with possibly different component types. -/
structure Pair (A : Type u) (B : Type v) : Type (max u v) where
  fst : A
  snd : B

#check Pair
#check Pair.fst
#check Pair.snd


-- ================================================================
-- Exercise 2
-- Problem (restated):
-- Define a function `Pair.swap` that takes a `Pair A B` and returns a
-- `Pair B A` with the components swapped.
-- ================================================================

/-- Swap the two components of a pair. -/
def Pair.swap {A : Type u} {B : Type v} : Pair A B → Pair B A
  | ⟨a, b⟩ => ⟨b, a⟩

#check Pair.swap
-- Pair.swap : {A : Type u} → {B : Type v} → Pair A B → Pair B A

-- quick tests
def p1 : Pair Nat String := ⟨42, "hello"⟩
#check Pair.swap p1
-- Pair String Nat

#eval (Pair.swap p1).fst   -- "hello"
#eval (Pair.swap p1).snd   -- 42

-- ================================================================
-- Exercise 3
-- Problem (restated):
-- Define a dependent type `chooseType : Bool → Type`
-- such that `chooseType true` is `Nat` and `chooseType false` is `String`.
-- Then define a function
--   f : (b : Bool) → chooseType b
-- such that `f true` is a natural number and `f false` is a string
-- ================================================================

def chooseType : Bool → Type
  | true  => Nat
  | false => String

def f : (b : Bool) → chooseType b
  | true  => (5 : Nat)
  | false => ("hello" : String)

#check f
#check f true   -- chooseType true  (definitionally Nat)
#check f false  -- chooseType false (definitionally String)

#eval f true
#eval f false

-- ============================================================
-- Exercise 4
-- Problem (restated):
-- Define a function
--   forget : Σ (n : Nat), Vec Nat n → List Nat
-- that takes a Sigma value representing a length `n` and a vector
-- `v : Vec Nat n`, and returns the vector turned into a list.
-- ============================================================

universe u'

inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

namespace Vec

def toList {α : Type u} : {n : Nat} → Vec α n → List α
  | 0,    .nil        => []
  | _,    .cons a v'  => a :: toList v'

end Vec

def forget : (Σ (n : Nat), Vec Nat n) → List Nat
  | ⟨_, v⟩ => Vec.toList v

-- quick tests
#eval forget ⟨0, (Vec.nil : Vec Nat 0)⟩
#eval forget ⟨1, (Vec.cons 5 Vec.nil)⟩
#eval forget ⟨2, (Vec.cons 7 (Vec.cons 5 Vec.nil))⟩   -- [7, 5]


-- ================================================================
-- Exercise 5
-- Problem (restated):
-- Define a function that computes the length of a list using `List.recOn`.
-- ===============================================================
def length {α} (L : List α) : Nat :=
  List.recOn L 0 (fun h t mt => 1 + mt)

-- ===============================================================
-- Exercise 6
-- Problem (restated):
-- Recall the definition of `Dyadic` from Slide Deck II.4.
-- - Instantiate `Zero` and `One`.
-- - Check that the iteration notation `f^[n]` works for your Dyadic.
-- ==============================================================

namespace Dyadic

inductive Dyadic where
  | zero    : Dyadic
  | add_one : Dyadic → Dyadic
  | half    : Dyadic → Dyadic
  | neg     : Dyadic → Dyadic
deriving Repr

open Dyadic

-- expose the three endofunctions we want to iterate
def add_one_fn : Dyadic → Dyadic := Dyadic.add_one
def half_fn : Dyadic → Dyadic := Dyadic.half

def double_fn : Dyadic → Dyadic
  | .zero        => .zero
  | .add_one x   => .add_one (.add_one (double_fn x))
  | .half x      => x
  | .neg x       => .neg (double_fn x)

-- instances requested (and the missing one that numerals actually need)
instance : Zero Dyadic := ⟨.zero⟩
instance : One Dyadic  := ⟨.add_one .zero⟩

def ofNat : Nat → Dyadic
  | 0     => .zero
  | n+1   => .add_one (ofNat n)

instance (n : Nat) : OfNat Dyadic n := ⟨ofNat n⟩

open Function

-- checks from the prompt (these should now elaborate cleanly)
#eval (add_one_fn^[8]) (0 : Dyadic)   -- 8
#eval (double_fn^[8])  (1 : Dyadic)   -- 256
#eval (half_fn^[8])    (1 : Dyadic)   -- 1/256 (as a dyadic term; see to_rat below)

end Dyadic

-- ============================================================
-- Exercise 7
-- Problem (restated):
-- Instantiate `HAdd` and `Add` for Dyadic.
-- Use a `sum` function to compute  ∑_{n=1}^8 n · 2^{-n}
-- and use `.to_rat` to check the answer.
-- ============================================================

namespace HW

inductive MyDyadic where
  | zero    : MyDyadic
  | add_one : MyDyadic → MyDyadic
  | half    : MyDyadic → MyDyadic
  | neg     : MyDyadic → MyDyadic

namespace MyDyadic

def double : MyDyadic → MyDyadic
  | .zero        => .zero
  | .add_one x   => .add_one (.add_one (double x))
  | .half x      => x
  | .neg x       => .neg (double x)

def add (x y : MyDyadic) : MyDyadic :=
  match y with
  | .zero       => x
  | .add_one y' => .add_one (add x y')
  | .half y'    => .half (add (double x) y')
  | .neg y'     => .neg (add (.neg x) y')

instance : HAdd MyDyadic MyDyadic MyDyadic where
  hAdd := add

instance : Add MyDyadic where
  add := add

-- This is the missing piece: `sum` (matches the slide pattern).
def sum (f : Nat → MyDyadic) : Nat → MyDyadic
  | 0     => f 0
  | n+1   => sum f n + f (n+1)

def one : MyDyadic := .add_one .zero

def pow2neg : Nat → MyDyadic
  | 0   => one
  | n+1 => .half (pow2neg n)

def nsmul (n : Nat) (x : MyDyadic) : MyDyadic :=
  match n with
  | 0   => .zero
  | k+1 => add x (nsmul k x)

def term : Nat → MyDyadic
  | 0 => .zero
  | n => nsmul n (pow2neg n)

def S : MyDyadic := sum term 8

def to_rat : MyDyadic → Rat
  | .zero      => (0 : Rat)
  | .add_one x => to_rat x + (1 : Rat)
  | .half x    => to_rat x / (2 : Rat)
  | .neg x     => - (to_rat x)

#eval to_rat S   -- should be 251/128

-- ============================================================
-- Exercise 8
-- Problem (restated):
-- Instantiate `HMul` and `Mul` for `MyDyadic`.
-- Define `product` similarly to how `sum` was defined.
-- Compute  Π_{n=1}^8  (n · 2^{-n})  with `MyDyadic` and use `to_rat`
-- to check the answer.
-- ============================================================f

namespace HW.MyDyadic

-- compact normal form: (n, k) means n / 2^k
def toNumExp : MyDyadic → Int × Nat
  | .zero =>
      (0, 0)
  | .add_one x =>
      let (n, k) := toNumExp x
      -- adding 1 = adding 2^k at this exponent level
      (n + Int.ofNat (Nat.pow 2 k), k)
  | .half x =>
      let (n, k) := toNumExp x
      (n, k + 1)
  | .neg x =>
      let (n, k) := toNumExp x
      (-n, k)

-- cancel as many factors of 2 from the numerator as possible (while k > 0)
def normNumExpAux (n : Int) : Nat → Int × Nat
  | 0 => (n, 0)
  | Nat.succ k =>
      if n % 2 = 0 then
        normNumExpAux (n / 2) k
      else
        (n, Nat.succ k)

def normNumExp : Int × Nat → Int × Nat
  | (n, k) => normNumExpAux n k

def fromNat : Nat → MyDyadic
  | 0     => .zero
  | n+1   => .add_one (fromNat n)

def halfPow : Nat → MyDyadic → MyDyadic
  | 0,   x => x
  | k+1, x => .half (halfPow k x)

def fromInt (z : Int) : MyDyadic :=
  if z < 0 then
    .neg (fromNat (Int.toNat (-z)))
  else
    fromNat (Int.toNat z)

def fromNumExp (p : Int × Nat) : MyDyadic :=
  let (n, k) := normNumExp p
  halfPow k (fromInt n)

-- multiplication that normalizes (so terms don’t explode)
def mul (x y : MyDyadic) : MyDyadic :=
  let (nx, kx) := toNumExp x
  let (ny, ky) := toNumExp y
  fromNumExp (nx * ny, kx + ky)

instance : HMul MyDyadic MyDyadic MyDyadic where
  hMul := mul

instance : Mul MyDyadic where
  mul := mul

-- Π_{i=1}^n f(i)
def product (f : Nat → MyDyadic) : Nat → MyDyadic
  | 0     => one
  | n+1   => product f n * f (n+1)

def P : MyDyadic := product term 8

#eval to_rat P   -- should be 315/268435456

end HW.MyDyadic

end MyDyadic
end HW
