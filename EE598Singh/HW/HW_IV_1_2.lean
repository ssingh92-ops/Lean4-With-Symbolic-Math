/-
HW_IV_1_2.lean
Sukhman Singh
EE598 — Homework IV.1 (Algebra) and IV.2 (Sets)

This file follows the course style of rebuilding basic structures in a temporary
namespace rather than using Mathlib's algebraic hierarchy directly. In this
portion, we work on IV.1 Algebra, proving uniqueness of the identity element
and uniqueness of inverses for our custom Group class.

The notation and proof style follow the lecture slides: additive notation,
typeclasses, and explicit tactic / calc proofs.

IV.2 Sets is reserved for later in this same file.
-/

import Mathlib

namespace Temp

/-!
## IV.1 Algebra
-/

universe u

/-
We rebuild the basic group structure inside `Temp` to avoid conflicting with
Mathlib's existing definitions.
-/
class Group (G : Type u) where
  op : G → G → G
  e : G
  inv : G → G
  assoc {a b c : G} : op (op a b) c = op a (op b c)
  id_left {a : G} : op e a = a
  inv_left {a : G} : op (inv a) a = e

class CommGroup (G : Type u) extends Group G where
  comm {a b : G} : op a b = op b a

/-
Use additive notation, as in the lecture slides.
-/
infixl:60 " + " => Group.op
prefix:95 "-" => Group.inv

open Group
open CommGroup

/-
Shared variables for theorem statements.
-/
variable {G : Type u} [Group G] {a b c : G}

/-
First derive a few standard lemmas from the axioms, following the lecture notes.
These are the same kinds of results shown in the screenshots and are used by
the homework exercises below.
-/

theorem Group.cancel_left : a + b = a + c → b = c := by
  intro h
  apply congrArg (fun t => (-a) + t) at h
  rw [← assoc] at h
  rw [inv_left] at h
  rw [id_left] at h
  rw [← assoc] at h
  rw [inv_left] at h
  rw [id_left] at h
  exact h

theorem Group.id_right : a + (e : G) = a := by
  apply Group.cancel_left (a := -a)
  calc
    (-a) + (a + (e : G))
        = ((-a) + a) + (e : G) := by rw [assoc]
    _ = (e : G) + (e : G) := by rw [inv_left]
    _ = (e : G) := by rw [id_left]
    _ = (-a) + a := by rw [inv_left]

theorem Group.inv_right : a + (-a) = (e : G) := by
  apply Group.cancel_left (a := -a)
  calc
    (-a) + (a + (-a))
        = ((-a) + a) + (-a) := by rw [assoc]
    _ = (e : G) + (-a) := by rw [inv_left]
    _ = -a := by rw [id_left]
    _ = (-a) + (e : G) := by rw [Group.id_right (a := -a)]

theorem Group.cancel_right : b + a = c + a → b = c := by
  intro h
  apply congrArg (fun t => t + (-a)) at h
  rw [assoc, assoc] at h
  rw [Group.inv_right (a := a)] at h
  rw [Group.id_right (a := b)] at h
  rw [Group.id_right (a := c)] at h
  exact h

-- ============================================================
-- Exercise 1
-- Problem (restated):
-- Show that the identity element of a group is unique:
--   theorem Group.id_unique {e' : G} : (∀ a, e' + a = a) → e = e'
--
-- Textual explanation:
-- - We assume `e'` is another left identity, meaning `e' + a = a`
--   for every element `a`.
-- - We then compare `e' + e` in two different ways.
-- - Using the derived theorem `id_right`, we get `e' + e = e'`.
-- - Using the hypothesis with `a := e`, we get `e' + e = e`.
-- - Since both expressions are equal to `e' + e`, it follows that
--   `e = e'`, so the identity element is unique.
-- ============================================================
theorem Group.id_unique {e' : G} : (∀ a, e' + a = a) → (e : G) = e' := by
  intro h
  have h1 : e' + (e : G) = e' := by
    rw [Group.id_right (a := e')]
  have h2 : e' + (e : G) = (e : G) := by
    simpa using h (e : G)
  calc
    (e : G) = e' + (e : G) := by symm; exact h2
    _ = e' := h1

-- ============================================================
-- Exercise 2
-- Problem (restated):
-- Show that inverses are unique:
--   theorem Group.inv_unique : b + a = e → c + a = e → b = c
--
-- Textual explanation:
-- - We assume both `b` and `c` are right inverses of the same element `a`.
-- - That means `b + a = e` and `c + a = e`.
-- - To conclude `b = c`, we use right cancellation.
-- - Since both `b + a` and `c + a` are equal to `e`, they are equal to
--   each other.
-- - Cancelling the common `a` on the right gives `b = c`.
-- - Therefore the inverse of an element is unique.
-- ============================================================
theorem Group.inv_unique : b + a = (e : G) → c + a = (e : G) → b = c := by
  intro hb hc
  apply Group.cancel_right (a := a)
  calc
    b + a = (e : G) := hb
    _ = c + a := by symm; exact hc


-- ============================================================
-- Exercise 3
-- Problem (restated):
-- Show that the product of two groups is again a group by defining:
--   instance Group.prod {G H : Type u} [Group G] [Group H] :
--     Group (G × H)
--
-- Textual explanation:
-- - The group operation on `G × H` is defined componentwise:
--   `(x₁, x₂) + (y₁, y₂) = (x₁ + y₁, x₂ + y₂)`.
-- - The identity element is the pair of identities `(e, e)`.
-- - The inverse of `(x₁, x₂)` is `(-x₁, -x₂)`.
-- - The group axioms are then proved componentwise as well.
-- - Associativity follows from associativity in each coordinate.
-- - Left identity and left inverse also follow coordinatewise from the
--   corresponding axioms in `G` and `H`.
-- - Therefore the cartesian product of two groups is a group.
-- ============================================================
instance Group.prod {G H : Type u} [Group G] [Group H] : Group (G × H) := {
  op x y := (x.1 + y.1, x.2 + y.2)
  e := (e, e)
  inv x := (-x.1, -x.2)
  assoc {a b c} := by
    cases a
    cases b
    cases c
    simp [Group.assoc]
  id_left {a} := by
    cases a
    simp [Group.id_left]
  inv_left {a} := by
    cases a
    simp [Group.inv_left]
}

/-
Needed setup for Exercise 4:
`Spin` is not in the file yet, so we define it here.
-/
inductive Spin where
  | up
  | dn

open Spin

def Spin.toggle : Spin → Spin
  | up => dn
  | dn => up

def spinOp (x y : Spin) : Spin :=
  match x, y with
  | up, dn => dn
  | dn, up => dn
  | _,  _  => up

instance Spin.inst_comm_group : CommGroup Spin := {
  op := spinOp
  e := up
  inv := id
  assoc {a b c} := by
    cases a <;> cases b <;> cases c <;> rfl
  id_left {a} := by
    cases a <;> rfl
  inv_left {a} := by
    cases a <;> rfl
  comm {a b} := by
    cases a <;> cases b <;> rfl
}

-- ============================================================
-- Exercise 4
-- Problem (restated):
-- Define the type `Spin`, instantiate it as a commutative group, and show:
--   example : e = (up, up)
--   example : -(up, up) = (up, up)
--   example (x : Spin × Spin) : -x + x = (up, up)
--
-- Textual explanation:
-- - We define `Spin` as a two-element type with constructors `up` and `dn`.
-- - The operation is defined so that `up` acts as the identity and every
--   element is its own inverse.
-- - This makes `Spin` into a commutative group.
-- - Once `Spin` has this group structure, the product `Spin × Spin` inherits
--   a group structure from Exercise 3.
-- - The first example states that the identity in `Spin × Spin` is `(up, up)`.
-- - The second example states that `(up, up)` is its own inverse.
-- - The third example is the general inverse law in `Spin × Spin`,
--   specialized to show that `-x + x = (up, up)`.
-- ============================================================
example : (e : Spin × Spin) = (up, up) := by
  rfl

example : -(up, up) = (up, up) := by
  rfl

example (x : Spin × Spin) : -x + x = (up, up) := by
  exact Group.inv_left

-- ============================================================
-- Exercise 5
-- Problem (restated):
-- Show
--   theorem factor_mul_inv_right : x * (-y) = -(x * y)
--
-- Textual explanation:
-- - We first use the additive inverse law to get `y + -y = e`.
-- - We then multiply both sides by `x`, giving
--   `x * (y + -y) = x * e`.
-- - By left distributivity, the left-hand side becomes
--   `x * y + x * (-y)`.
-- - By the `mul_zero` identity from the notes, the right-hand side is `e`.
-- - So we obtain `x * y + x * (-y) = e`.
-- - Finally, we add `-(x * y)` to both sides and simplify using the
--   group identities.
-- ============================================================

class Monoid (M : Type u) where
  mul : M → M → M
  one : M
  mul_assoc {a b c : M} : mul (mul a b) c = mul a (mul b c)
  mul_id_left {a : M} : mul one a = a
  mul_id_right {a : M} : mul a one = a

class Ring (R : Type u) extends CommGroup R, Monoid R where
  l_distrib {x y z : R} : mul x (op y z) = op (mul x y) (mul x z)
  r_distrib {x y z : R} : mul (op y z) x = op (mul y x) (mul z x)

class CommRing (R : Type u) extends Ring R where
  mulcomm {x y : R} : mul x y = mul y x

variable {R : Type u} [CommRing R]

infixl:80 " * " => Monoid.mul

open Monoid Ring CommRing Group

theorem Ring.add_left (h : y = z) (x : R) : x + y = x + z := by
  rw [h]

theorem Ring.mul_zero (x : R) : x * (e : R) = e := by
  have h0 := l_distrib (x := x) (y := (e : R)) (z := (e : R))
  have h := Ring.add_left h0 (-(x * (e : R)))
  rw [id_left] at h
  rw [inv_left] at h
  rw [← assoc] at h
  rw [inv_left] at h
  rw [id_left] at h
  exact h.symm

theorem factor_mul_inv_right (x y : R) : x * (-y) = -(x * y) := by
  have h0 : y + (-y) = (e : R) := by
    rw [Group.inv_right (a := y)]
  have h1 : x * (y + (-y)) = x * (e : R) := by
    rw [h0]
  rw [l_distrib, Ring.mul_zero] at h1
  have h2 := Ring.add_left h1 (-(x * y))
  rw [← assoc] at h2
  rw [inv_left] at h2
  rw [id_left] at h2
  rw [Group.id_right (a := -(x * y))] at h2
  exact h2

-- ============================================================
-- Exercise 6
-- Problem (restated):
-- Show
--   example (x y : Spin) : x * y + x = x * (y + Spin.dn)
--
-- Textual explanation:
-- - We first define multiplication on `Spin`.
-- - We then instantiate `Spin` as a monoid, with multiplicative identity `dn`.
-- - Next we instantiate `Spin` as a ring by proving left and right
--   distributivity by case splitting.
-- - Once `Spin` is a ring, we rewrite `x` as `x * dn` using the
--   multiplicative right identity.
-- - Then the left-hand side becomes `x * y + x * dn`.
-- - By distributivity, this equals `x * (y + dn)`.
-- - To avoid notation conflicts in the file, we write multiplication
--   explicitly as `Monoid.mul`.
-- ============================================================

def Spin.mul (a b : Spin) : Spin :=
  match a, b with
  | Spin.dn, Spin.dn => Spin.dn
  | _, _ => Spin.up

instance Spin.inst_monoid : Monoid Spin := {
  one := Spin.dn
  mul := Spin.mul
  mul_assoc {x y z} := by
    cases x <;> cases y <;> cases z <;> rfl
  mul_id_left {x} := by
    cases x <;> rfl
  mul_id_right {x} := by
    cases x <;> rfl
}

instance Spin.inst_ring : Ring Spin := {
  l_distrib {x y z} := by
    cases x <;> cases y <;> cases z <;> rfl
  r_distrib {x y z} := by
    cases x <;> cases y <;> cases z <;> rfl
}

example (x y : Spin) :
    Monoid.mul x y + x = Monoid.mul x (y + Spin.dn) := by
  cases x <;> cases y <;> rfl

-- ============================================================
-- Exercise 7
-- Problem (restated):
-- Complete the development showing `ℕ → R` forms a ring.
--
-- Textual explanation:
-- - Ring-valued sequences are given pointwise operations.
-- - Addition and additive inverse are defined pointwise, so `ℕ → R`
--   forms a commutative group whenever `R` does.
-- - Multiplication and multiplicative identity are also defined
--   pointwise, so `ℕ → R` forms a monoid whenever `R` does.
-- - To prove `ℕ → R` is a ring, it remains to check left and right
--   distributivity.
-- - Since all operations are pointwise, each ring law is proved by
--   `funext n` and then applying the corresponding law in `R`.
-- ============================================================

instance Seq.inst_comm_group {R : Type u} [CommGroup R] : CommGroup (ℕ → R) := {
  op f g n := f n + g n
  e n := e
  inv f n := -(f n)
  assoc {f g h} := by
    funext n
    exact assoc
  id_left {f} := by
    funext n
    exact id_left
  inv_left {f} := by
    funext n
    exact inv_left
  comm {f g} := by
    funext n
    exact comm
}

instance Seq.inst_monoid {R : Type u} [Monoid R] : Monoid (ℕ → R) := {
  mul f g n := (f n) * (g n)
  one n := one
  mul_assoc {f g h} := by
    funext n
    exact mul_assoc
  mul_id_left {f} := by
    funext n
    rw [mul_id_left]
  mul_id_right {f} := by
    funext n
    rw [mul_id_right]
}

instance Seq.inst_ring {R : Type u} [Ring R] : Ring (ℕ → R) := {
  l_distrib {x y z} := by
    funext n
    exact l_distrib
  r_distrib {x y z} := by
    funext n
    exact r_distrib
}

-- ============================================================
-- Exercise 8
-- Problem (restated):
-- Show that if `R` is a commutative ring, then so is `ℕ → R`.
--
-- Textual explanation:
-- - Exercise 7 already shows that `ℕ → R` is a ring when `R` is a ring.
-- - So to obtain a commutative ring structure, the only new property
--   to prove is commutativity of multiplication.
-- - Multiplication on sequences is pointwise, so this reduces to
--   commutativity in the codomain ring `R` at each natural number `n`.
-- - We reuse the previously defined ring structure and only add the
--   new commutativity field.
-- ============================================================

instance Seq.inst_commring {R : Type u} [CommRing R] : CommRing (ℕ → R) := {
  mulcomm {x y} := by
    funext n
    exact mulcomm
}

-- ============================================================
-- Exercise 9 (Optional)
-- Problem (restated):
-- Define the principal ideal generated by `x : R`:
--
--   def PrincipalIdeal {R : Type u} [CommRing R] (x : R) : Ideal R := { ... }
--
-- Textual explanation:
-- - An element `y` belongs to the principal ideal generated by `x`
--   if there exists some `r : R` such that `y = x * r`.
-- - To show this defines an ideal, we prove three properties.
-- - First, zero is in the ideal because `x * e = e` by the `mul_zero`
--   theorem from the earlier ring exercises.
-- - Second, the ideal is closed under `-y + z` by writing
--   `y = x * a` and `z = x * b`, then factoring out `x`.
-- - Third, the ideal is closed under multiplication on both sides,
--   again by rewriting with associativity and commutativity.
-- - Since the ring is commutative, both left and right absorption
--   stay inside the same principal ideal.
-- ============================================================

structure Ideal (R : Type u) [CommRing R] where
  I : R → Prop
  has_zero : I e
  closed {x y : R} : I x → I y → I (-x + y)
  absorb {r x : R} : I x → I (r * x) ∧ I (x * r)

def PrincipalIdeal {R : Type u} [CommRing R] (x : R) : Ideal R := {
  I y := ∃ r : R, y = x * r

  has_zero := by
    refine ⟨e, ?_⟩
    symm
    exact Ring.mul_zero x

  closed := by
    intro y z hy hz
    rcases hy with ⟨a, rfl⟩
    rcases hz with ⟨b, rfl⟩
    refine ⟨(-a) + b, ?_⟩
    calc
      -(x * a) + x * b
          = x * (-a) + x * b := by
              rw [← factor_mul_inv_right (x := x) (y := a)]
      _ = x * ((-a) + b) := by
              rw [← l_distrib]

  absorb := by
    intro r y hy
    rcases hy with ⟨a, rfl⟩
    constructor
    · refine ⟨r * a, ?_⟩
      calc
        r * (x * a)
            = (r * x) * a := by rw [Monoid.mul_assoc]
        _ = (x * r) * a := by rw [CommRing.mulcomm (x := r) (y := x)]
        _ = x * (r * a) := by rw [← Monoid.mul_assoc]
    · refine ⟨a * r, ?_⟩
      calc
        (x * a) * r
            = x * (a * r) := by rw [Monoid.mul_assoc]
}

-- ============================================================
-- Field setup needed for Exercises 10 and 12
--
-- Textual explanation:
-- - Exercises 10 and 12 use a custom field structure extending the
--   custom commutative ring structure from this homework file.
-- - We also need a custom nontriviality class, since the proof that
--   `1 ≠ 0` uses the existence of two distinct elements.
-- - The field structure includes a multiplicative inverse operation,
--   the inverse law for nonzero elements, and the convention `0⁻¹ = 0`.
-- ============================================================

class Nontrivial (X : Type u) where
  exists_pair_ne : ∃ x y : X, x ≠ y

class Field (F : Type u) extends CommRing F, Nontrivial F where
  minv : F → F
  mul_inv_prop {x : F} : x ≠ e → mul x (minv x) = one
  minv_zero : minv e = e

postfix:max "⁻¹" => Field.minv

-- ============================================================
-- Exercise 10
-- Problem (restated):
-- Show
--   theorem one_inv : (one : F)⁻¹ = one
--
-- Textual explanation:
-- - We work in the custom `Field` hierarchy from this homework file.
-- - First we prove helper lemmas: right multiplicative identity,
--   zero on the left, and the left-side inverse law.
-- - We then prove `1 ≠ 0` using nontriviality, following the notes.
-- - Finally, since `1 * 1⁻¹ = 1`, uniqueness of inverses gives
--   `1⁻¹ = 1`.
-- ============================================================

theorem field_mul_id_right {F : Type u} [Field F] (x : F) :
    Monoid.mul x (Monoid.one : F) = x := by
  calc
    Monoid.mul x (Monoid.one : F)
        = Monoid.mul (Monoid.one : F) x := by
            exact CommRing.mulcomm (x := x) (y := (Monoid.one : F))
    _ = x := by
            exact Monoid.mul_id_left (a := x)

theorem field_zero_mul {F : Type u} [Field F] (x : F) :
    Monoid.mul (Group.e : F) x = (Group.e : F) := by
  calc
    Monoid.mul (Group.e : F) x
        = Monoid.mul x (Group.e : F) := by
            exact CommRing.mulcomm (x := (Group.e : F)) (y := x)
    _ = (Group.e : F) := by
            exact Ring.mul_zero (x := x)

theorem field_inv_mul_prop {F : Type u} [Field F] {x : F}
    (hx : x ≠ (Group.e : F)) :
    Monoid.mul (Field.minv x) x = (Monoid.one : F) := by
  calc
    Monoid.mul (Field.minv x) x
        = Monoid.mul x (Field.minv x) := by
            exact CommRing.mulcomm (x := (Field.minv x)) (y := x)
    _ = (Monoid.one : F) := by
            exact Field.mul_inv_prop hx

theorem field_one_ne_e {F : Type u} [Field F] :
    (Monoid.one : F) ≠ (Group.e : F) := by
  intro h
  obtain ⟨x, y, hxy⟩ := (inferInstance : Nontrivial F).exists_pair_ne
  have hx : x = (Group.e : F) := by
    calc
      x = Monoid.mul x (Monoid.one : F) := by
            symm
            exact field_mul_id_right x
      _ = Monoid.mul x (Group.e : F) := by rw [h]
      _ = (Group.e : F) := by
            exact Ring.mul_zero (x := x)
  have hy : y = (Group.e : F) := by
    calc
      y = Monoid.mul y (Monoid.one : F) := by
            symm
            exact field_mul_id_right y
      _ = Monoid.mul y (Group.e : F) := by rw [h]
      _ = (Group.e : F) := by
            exact Ring.mul_zero (x := y)
  exact hxy (Eq.trans hx hy.symm)

theorem field_inv_unique_right {F : Type u} [Field F] {c d : F}
    (hc : c ≠ (Group.e : F))
    (h : Monoid.mul c d = (Monoid.one : F)) :
    d = Field.minv c := by
  calc
    d = Monoid.mul (Monoid.one : F) d := by
          symm
          exact Monoid.mul_id_left (a := d)
    _ = Monoid.mul (Monoid.mul (Field.minv c) c) d := by
          rw [field_inv_mul_prop hc]
    _ = Monoid.mul (Field.minv c) (Monoid.mul c d) := by
          exact Monoid.mul_assoc (a := (Field.minv c)) (b := c) (c := d)
    _ = Monoid.mul (Field.minv c) (Monoid.one : F) := by
          rw [h]
    _ = Field.minv c := by
          exact field_mul_id_right (Field.minv c)

theorem one_inv {F : Type u} [Field F] :
    Field.minv (Monoid.one : F) = (Monoid.one : F) := by
  have h1 : (Monoid.one : F) ≠ (Group.e : F) := field_one_ne_e
  have h2 : Monoid.mul (Monoid.one : F) (Monoid.one : F) = (Monoid.one : F) := by
    exact field_mul_id_right (Monoid.one : F)
  have h3 : (Monoid.one : F) = Field.minv (Monoid.one : F) := by
    exact field_inv_unique_right h1 h2
  exact h3.symm

-- ============================================================
-- Exercise 11
-- Problem (restated):
-- Instantiate `ℤ` as a `CommRing` using the custom definitions in
-- this file, not Mathlib's built-in ring class.
--
-- Textual explanation:
-- - We use the usual integer operations for addition, negation,
--   multiplication, zero, and one.
-- - The additive and multiplicative laws are proved using standard
--   integer identities.
-- - This gives a concrete example of a commutative ring in the custom
--   hierarchy of this homework file.
-- ============================================================

instance Int.inst_commring : CommRing ℤ := {
  op := Int.add
  e := 0
  inv := Int.neg

  assoc {a b c} := by
    simpa using Int.add_assoc a b c
  id_left {a} := by
    simpa using Int.zero_add a
  inv_left {a} := by
    change (-a) + a = (0 : ℤ)
    simp
  comm {a b} := by
    simpa using Int.add_comm a b

  mul := Int.mul
  one := 1

  mul_assoc {a b c} := by
    simpa using Int.mul_assoc a b c
  mul_id_left {a} := by
    simpa using Int.one_mul a
  mul_id_right {a} := by
    simpa using Int.mul_one a

  l_distrib {x y z} := by
    simpa using Int.mul_add x y z
  r_distrib {x y z} := by
    simpa using Int.add_mul y z x

  mulcomm {x y} := by
    simpa using Int.mul_comm x y
}

-- ============================================================
-- Exercise 12 (Optional)
-- Problem (restated):
-- Show
--   (a * b)⁻¹ = a⁻¹ * b⁻¹
--
-- Textual explanation:
-- - First we prove that if `a ≠ 0` and `a * b = 0`, then `b = 0`.
-- - From that we get that the product of two nonzero elements is nonzero.
-- - Then we split into cases on whether `a = 0` or `b = 0`.
-- - In the nonzero case, we prove directly that `a⁻¹ * b⁻¹` is an
--   inverse of `a * b`, and then use uniqueness of inverses.
-- ============================================================

theorem field_mul_eq_zero_right {F : Type u} [Field F] {a b : F}
    (ha : a ≠ (Group.e : F))
    (h : Monoid.mul a b = (Group.e : F)) :
    b = (Group.e : F) := by
  calc
    b = Monoid.mul (Monoid.one : F) b := by
          symm
          exact Monoid.mul_id_left (a := b)
    _ = Monoid.mul (Monoid.mul (Field.minv a) a) b := by
          rw [field_inv_mul_prop ha]
    _ = Monoid.mul (Field.minv a) (Monoid.mul a b) := by
          exact Monoid.mul_assoc (a := (Field.minv a)) (b := a) (c := b)
    _ = Monoid.mul (Field.minv a) (Group.e : F) := by
          rw [h]
    _ = (Group.e : F) := by
          exact Ring.mul_zero (x := (Field.minv a))

theorem field_mul_ne_zero {F : Type u} [Field F] {a b : F}
    (ha : a ≠ (Group.e : F))
    (hb : b ≠ (Group.e : F)) :
    Monoid.mul a b ≠ (Group.e : F) := by
  intro h
  have hb' : b = (Group.e : F) := field_mul_eq_zero_right ha h
  exact hb hb'

theorem mul_inv_mul {F : Type u} [Field F] (a b : F) :
    Field.minv (Monoid.mul a b) =
      Monoid.mul (Field.minv a) (Field.minv b) := by
  by_cases ha : a = (Group.e : F)
  · rw [ha, field_zero_mul b, Field.minv_zero, field_zero_mul (Field.minv b)]
  · by_cases hb : b = (Group.e : F)
    · rw [hb, Ring.mul_zero (x := a), Field.minv_zero, Ring.mul_zero (x := (Field.minv a))]
    · have hab : Monoid.mul a b ≠ (Group.e : F) := field_mul_ne_zero ha hb
      have hprod :
          Monoid.mul (Monoid.mul a b)
            (Monoid.mul (Field.minv a) (Field.minv b))
            = (Monoid.one : F) := by
        calc
          Monoid.mul (Monoid.mul a b)
            (Monoid.mul (Field.minv a) (Field.minv b))
              = Monoid.mul
                  (Monoid.mul (Monoid.mul a b) (Field.minv a))
                  (Field.minv b) := by
                    exact (Monoid.mul_assoc
                      (a := (Monoid.mul a b))
                      (b := (Field.minv a))
                      (c := (Field.minv b))).symm
          _ = Monoid.mul
                (Monoid.mul a (Monoid.mul b (Field.minv a)))
                (Field.minv b) := by
                  exact congrArg
                    (fun t => Monoid.mul t (Field.minv b))
                    (Monoid.mul_assoc (a := a) (b := b) (c := (Field.minv a)))
          _ = Monoid.mul
                (Monoid.mul a (Monoid.mul (Field.minv a) b))
                (Field.minv b) := by
                  rw [CommRing.mulcomm (x := b) (y := (Field.minv a))]
          _ = Monoid.mul
                (Monoid.mul (Monoid.mul a (Field.minv a)) b)
                (Field.minv b) := by
                  exact congrArg
                    (fun t => Monoid.mul t (Field.minv b))
                    ((Monoid.mul_assoc (a := a) (b := (Field.minv a)) (c := b)).symm)
          _ = Monoid.mul
                (Monoid.mul (Monoid.one : F) b)
                (Field.minv b) := by
                  rw [Field.mul_inv_prop ha]
          _ = Monoid.mul b (Field.minv b) := by
                  rw [Monoid.mul_id_left]
          _ = (Monoid.one : F) := by
                  exact Field.mul_inv_prop hb
      have huniq :
          Monoid.mul (Field.minv a) (Field.minv b)
            = Field.minv (Monoid.mul a b) := by
        exact field_inv_unique_right hab hprod
      exact huniq.symm

/-!
## IV.2 Sets

Reserved for the sets portion of Homework IV.
-/

-- ============================================================
-- Exercise 1
-- Problem (restated):
-- Define addition on the subtype `Evens` of natural numbers,
-- and prove associativity:
--
--   def Evens.add (x y : Evens) : Evens := ...
--
--   def Evens.add_assoc {x y z : Evens} :
--     add x (add y z) = add (add x y) z := ...
--
-- Textual explanation:
-- - We represent the even natural numbers as a subtype.
-- - An element of `Evens` is a natural number together with a proof
--   that it is equal to `2 * k` for some natural number `k`.
-- - To define addition, we add the underlying natural numbers.
-- - We then prove the result is still even by extracting witnesses
--   for the two inputs and combining them.
-- - To prove associativity, we use `Subtype.ext` and reduce the goal
--   to the usual associativity of addition on natural numbers.
-- ============================================================

def Evens := { n : ℕ // ∃ k, n = Nat.mul 2 k }

def Evens.add (x y : Evens) : Evens :=
  ⟨x.1 + y.1, by
    rcases x.2 with ⟨kx, hkx⟩
    rcases y.2 with ⟨ky, hky⟩
    refine ⟨kx + ky, ?_⟩
    rw [hkx, hky]
    exact (Nat.mul_add 2 kx ky).symm
  ⟩

def Evens.add_assoc {x y z : Evens} :
    Evens.add x (Evens.add y z) = Evens.add (Evens.add x y) z := by
  apply Subtype.ext
  exact (Nat.add_assoc x.1 y.1 z.1).symm

-- ============================================================
-- Exercise 2
-- Problem (restated):
-- Using first order logic (and not Mathlib's set theorems), show:
--
--   example : A ⊆ C → B ⊆ C → A ∪ B ⊆ C := ...
--   example : A ⊆ B → B ⊆ C → A ⊆ C := ...
--
-- Textual explanation:
-- - The subset relation is just implication:
--   `A ⊆ B` means `∀ x, A x → B x`.
-- - For the first statement, if `x ∈ A ∪ B`, then either `x ∈ A`
--   or `x ∈ B`.
-- - In the left case, use the hypothesis `A ⊆ C`.
-- - In the right case, use the hypothesis `B ⊆ C`.
-- - For the second statement, membership in `A` implies membership in `B`,
--   and then membership in `B` implies membership in `C`.
-- - So the second result is just transitivity of implication.
-- ============================================================

example : Set.Subset A C → Set.Subset B C → Set.Subset (A ∪ B) C := by
  intro hAC hBC x hx
  cases hx with
  | inl hxA => exact hAC hxA
  | inr hxB => exact hBC hxB

example : Set.Subset A B → Set.Subset B C → Set.Subset A C := by
  intro hAB hBC x hxA
  exact hBC (hAB hxA)

-- ============================================================
-- Exercise 3
-- Problem (restated):
-- Show that image distributes over union:
--
--   example {f : α → β} : f '' (A ∪ B) = f '' A ∪ f '' B := ...
--
-- Textual explanation:
-- - To prove two sets are equal, it is enough to prove each is a subset
--   of the other.
-- - If `y ∈ f '' (A ∪ B)`, then there is some `x` with `f x = y`
--   and `x ∈ A ∪ B`.
-- - So either `x ∈ A` or `x ∈ B`, which puts `y` into `f '' A ∪ f '' B`.
-- - Conversely, if `y ∈ f '' A ∪ f '' B`, then either `y` comes from
--   some `x ∈ A` or from some `x ∈ B`.
-- - In either case, that same `x` lies in `A ∪ B`, so `y ∈ f '' (A ∪ B)`.
-- ============================================================

example {f : α → β} : f '' (A ∪ B) = f '' A ∪ f '' B := by
  apply subset_antisymm_iff.mpr
  constructor
  · intro y hy
    rcases hy with ⟨x, hxAB, rfl⟩
    cases hxAB with
    | inl hxA =>
        exact Or.inl ⟨x, hxA, rfl⟩
    | inr hxB =>
        exact Or.inr ⟨x, hxB, rfl⟩
  · intro y hy
    cases hy with
    | inl hyA =>
        rcases hyA with ⟨x, hxA, rfl⟩
        exact ⟨x, Or.inl hxA, rfl⟩
    | inr hyB =>
        rcases hyB with ⟨x, hxB, rfl⟩
        exact ⟨x, Or.inr hxB, rfl⟩

-- ============================================================
-- Exercise 4
-- Problem (restated):
-- Show that preimage distributes over intersection:
--
--   example {f : α → β} : f⁻¹' (D ∩ E) = f⁻¹' D ∩ f⁻¹' E := ...
--
-- Textual explanation:
-- - An element `x` is in the preimage `f⁻¹' S` exactly when `f x ∈ S`.
-- - So `x ∈ f⁻¹' (D ∩ E)` means `f x ∈ D ∩ E`, which means both
--   `f x ∈ D` and `f x ∈ E`.
-- - That is exactly the statement that `x ∈ f⁻¹' D ∩ f⁻¹' E`.
-- - The reverse direction is the same reasoning in the other order.
-- - So the two sets are equal by pointwise logical equivalence.
-- ============================================================

example {f : α → β} : f⁻¹' (D ∩ E) = f⁻¹' D ∩ f⁻¹' E := by
  apply subset_antisymm_iff.mpr
  constructor
  · intro x hx
    exact ⟨hx.1, hx.2⟩
  · intro x hx
    exact ⟨hx.1, hx.2⟩

-- ============================================================
-- Exercise 5
-- Problem (restated):
-- Prove the following properties of `Fin`:
--
--   example : Fin 0 → False := ...
--   example (x : Fin 2) : x = 0 ∨ x = 1 := ...
--   example (n : ℕ) (x y : Fin n) : x = y ↔ x.val = y.val := ...
--
-- Textual explanation:
-- - An element of `Fin n` is a natural number together with a proof
--   that it is strictly less than `n`.
-- - Since no natural number is less than `0`, the type `Fin 0` is empty.
-- - For `Fin 2`, the only possible values are `0` and `1`.
-- - Finally, two `Fin n` elements are equal exactly when their underlying
--   values are equal, since the proof component is proposition-valued.
-- ============================================================

example : Fin 0 → False := by
  intro x
  exact Nat.not_lt_zero x.val x.isLt

example (x : Fin 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  have h : v = 0 ∨ v = 1 := by
    omega
  cases h with
  | inl h0 =>
      left
      subst h0
      rfl
  | inr h1 =>
      right
      subst h1
      rfl

example (n : ℕ) (x y : Fin n) : x = y ↔ x.val = y.val := by
  constructor
  · intro h
    rw [h]
  · intro h
    exact Fin.ext h

-- ============================================================
-- Exercise 6
-- Problem (restated):
-- Define the equivalence
--
--   def equiv_subtype {n : ℕ} : Fin n ≃ { x : ℕ | x < n } := ...
--
-- Textual explanation:
-- - Both `Fin n` and the subtype `{x : ℕ | x < n}` package the same
--   information: a natural number together with a proof that it is
--   less than `n`.
-- - So the equivalence simply sends an element to itself, viewed in the
--   other representation, and similarly in the reverse direction.
-- - The inverse laws are immediate by cases.
-- ============================================================

def equiv_subtype {n : ℕ} : Fin n ≃ { x : ℕ | x < n } := {
  toFun := fun x => ⟨x.val, x.isLt⟩
  invFun := fun x => ⟨x.val, x.property⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl
}

-- ============================================================
-- Exercise 7
-- Problem (restated):
-- Use the above equivalence to show
--
--   theorem equiv_same_size {n m : ℕ} (eq : Fin n ≃ Fin m) : n = m := ...
--
-- Textual explanation:
-- - The equivalence from Exercise 6 identifies `Fin n` with the subtype
--   `{x : ℕ | x < n}`.
-- - Intuitively, this means `Fin n` has exactly `n` elements.
-- - An equivalence `Fin n ≃ Fin m` therefore forces the two finite
--   types to have the same number of elements.
-- - We use Mathlib's cardinality theorem for finite types to conclude
--   `n = m`.
-- ============================================================

theorem equiv_same_size {n m : ℕ} (eq : Fin n ≃ Fin m) : n = m := by
  simpa using Fintype.card_congr eq
end Temp
