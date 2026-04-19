import Mathlib

-- ============================================================
-- Exercise 2
-- Problem (restated):
-- Define a lambda function that takes an argument and returns its square.
-- ============================================================

def h : Nat → Nat :=
  fun x => x * x

-- ============================================================
-- Exercise 3
-- Problem (restated):
-- Evaluate the following expressions using the function `h` defined above:
--   #eval h (h (h 2))
-- ============================================================

#eval h (h (h 2))
  -- expected output: 256

-- ============================================================
-- Exercise 4
-- Problem (restated):
-- Define Ω in Lean and explain what happens.
--
-- Slide version (untyped lambda calculus):
--   Ω := (λ x => x x)
--   Ω Ω loops forever.
--
-- Here, I’m going to write that same definition in Lean.

namespace Temp

-- Ω := λ x => x x
-- def Ω := (fun x => x x)
-- LEAN Response: Function expected at x but this term has type ?m.7 Note: Expected
-- a function because this term is being applied to the argument

-- and then Ω applied to itself
-- def ΩΩ := Ω Ω
-- LEAN Response: Unknown identifier `Ω` Error code: lean.unknownIdentifier

-- try inspecting / running
-- #check Ω
-- LEAN Response: Unknown identifier `Ω` Error code: lean.unknownIdentifier

-- #check ΩΩ
-- LEAN Response: Unknown identifier `Ω` Error code: lean.unknownIdentifier

-- #eval ΩΩ
-- LEAN Response: Unknown identifier `Ω` Error code: lean.unknownIdentifier

end Temp

-- What happens in Lean (typed / total):
-- 1) `def Ω := (fun x => x x)` FAILS to typecheck.
--    Reason: Lean is *typed*, so to apply `x` to `x`, Lean needs:
--        x : α → β   and also   x : α
--    i.e. the SAME `x` must be both a function type and an argument type.
--    In the untyped lambda calculus, “everything is a function”, so `x x` is fine.
--    In Lean, there is no type `α` with α = α → β (Lean blocks this kind of
--    “self-application” in the simple typed setting working in)....
--    aka avoiding the currying paradox.
--
--    That’s exactly what the error is saying:
--    “Function expected at x but this term has type ?m.7”
--    Meaning: Lean picked some type for `x` (a metavariable like `?m.7`),
--    but it cannot justify that `x` is a function, so `x x` is illegal.
--
-- 2) Because `def Ω := ...` failed, Ω was NEVER defined.
--    So every later reference (`ΩΩ := Ω Ω`, `#check Ω`, `#eval ΩΩ`) produces:
--       "Unknown identifier `Ω`"
--    That’s not a *new* problem—it's just fallout from the first failure.
--
-- Bottom line:
-- - In *untyped* lambda calculus, Ω exists and Ω Ω diverges.
-- - In Lean’s normal typed world, Ω is not definable as `fun x => x x`,
--   so can’t even build the diverging term in the first place.
-- ============================================================

-- ============================================================
-- Exercise 5
/-
Questions for Leonardo de Moura (Keynote Q&A) — EE598
Context: Lean 4, solver-backed verification, automation, and scaling

Q1 — “simp → solver” as architecture (preprocessing + certified decision procedures)
Problem (restated):
In the popcount example, the workflow appears to be:
  (1) `simp`-style preprocessing / normalization to expose a solver-friendly core theory, then
  (2) a decision procedure (e.g., bitblasting/SAT/SMT) that returns a certificate which Lean checks.

Question:
In solver-backed workflows (bitvectors, arithmetic, etc.), what engineering invariants determine
whether a step belongs in `simp`-style normalization versus a certified decision procedure?
Concretely, what criteria do you use to balance:
  (i) termination/controllability of rewriting (avoid rewrite blow-up),
  (ii) semantic transparency (avoid “proving by encoding artifact”), and
  (iii) faithfulness of the final encoding so the certificate proves the intended theorem?

Follow-up:
At large scale, what is the most common “automation collapse” mode you expect:
rewrite blow-up, poor simp-lemma curation/metadata discipline, or spec/encoding mismatch?

References (background reading):
https://cacm.acm.org/research/the-lean-theorem-prover-system/
https://leanprover.github.io/papers/lean4.pdf


Q2 — “Trust” beyond kernel soundness: intent drift via elaboration
Problem (restated):
Even if the kernel is sound, practice can fail when the elaborated term diverges from human intent
due to implicit mechanisms (coercions, typeclass inference, definitional unfolding,
notation/numerals).

Question:
If Lean is viewed as a “compiler” from human-written syntax to a kernel-checked term,
what are the top 2–3 elaboration-time mechanisms that most often cause “proved the wrong thing”
failures in real developments?
For example:
  (1) instance/typeclass selection drift under changing imports,
  (2) coercions/notation/numerals silently changing the statement,
  (3) definitional equality (defeq) hiding large computations or changing what rewriting exposes.

Follow-up:
What concrete workflows/tools do you recommend to make the elaborated term auditable
(e.g., surfacing inserted coercions/instances, controlling simp sets, import hygiene),
and what improvements would most reduce “semantic drift” at scale?

References (background reading):
https://leanprover.github.io/papers/lean4.pdf
https://arxiv.org/abs/1910.09336


Q3 — Extensibility vs maintainability at “100M LOC mathlib scale”
Problem (restated):
As mathlib scales, the limiting factor may be less about kernel foundations and more about
dependency sprawl, compilation/elaboration throughput, and proof automation fragility.

Question:
Based on how mathlib fails today (typeclass/tactic brittleness, simp-set hygiene,
dependency entanglement),
what do you expect to be the dominant limiter at ~100M LOC:
  (A) compilation/elaboration throughput,
  (B) dependency sprawl (“everything depends on everything”), or
  (C) automation instability/fragility?

Follow-up:
Which mechanisms seem most promising in practice:
  - stronger package boundaries and dependency tooling,
  - caching strategies / incremental elaboration,
  - proof term minimization / certificate reuse,
  - “automation contracts” (controlled simp sets + lint-enforced invariants),
  - or other governance/tooling approaches?

And a pointed build/ecosystem question:
Do you expect the long-run solution to resemble a Rust-like crate ecosystem with hard boundaries,
or a monorepo with heavy build tooling—given Lean’s elaboration, typeclass inference, and
tactic stack?

References (background reading):
https://leanprover-community.github.io/papers/mathlib-analysis.pdf
https://leanprover.github.io/papers/lean4.pdf
-/
