import Mathlib
import PrimeNumberTheoremAnd.Mathlib.Algebra.Notation.SupportAristotle

set_option lang.lemmaCmd true

open MeasureTheory Set Real
open scoped ContDiff

-- This version makes the support of Ψ explicit, and this is easier for some later proofs
lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧
    Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧ (Function.support Ψ = Set.Ioo a d) := by
  admit

/-!
Let $\nu$ be a bumpfunction.
-/
/-- **SmoothExistence**

There exists a smooth (once differentiable would be enough), nonnegative ``bumpfunction'' $\nu$,
   supported in $[1/2,2]$ with total mass one:
  $$
  \int_0^\infty \nu(x)\frac{dx}{x} = 1.
  $$

PROVIDED SOLUTION:
Same idea as Urysohn-type argument.
-/
lemma SmoothExistence : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  admit