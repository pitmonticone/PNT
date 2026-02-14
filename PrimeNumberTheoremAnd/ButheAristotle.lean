import Mathlib
import PrimeNumberTheoremAnd.SecondaryDefinitionsAristotle

/-!
# The estimates of Buthe



In this section we collect some results from Buthe's paper [reference], which provides explicit estimates on $\psi(x)$, $\theta(x)$, and $\pi(x)$.

TODO: Add more results and proofs here, and reorganize the blueprint
-/


namespace Buthe

open MeasureTheory Real Chebyshev

-- TODO: enter in other results from Buthe's paper than Theorem 2.
/-- **Buthe Equation (1.4)**

$\pi^*(x) = \sum_{k \geq 1} \pi(x^{1/k}) / k$.
-/
noncomputable def pi_star (x : ℝ) : ℝ :=
  ∑' (k : ℕ), pi (x ^ (1 / (k:ℝ))) / (k:ℝ)
/-- **Buthe Theorem 2(a)**

If $11 < x \leq 10^{19}$, then $|x - \psi(x)| \leq 0.94\sqrt{x}$.
-/
theorem theorem_2a {x : ℝ} (hx1 : 11 < x) (hx2 : x ≤ 10 ^ 19) :
    Eψ x ≤ 0.94 / sqrt x := by sorry

/-- **Buthe Theorem 2(b)**

If $1423 \leq x \leq 10^{19}$, then $x - \vartheta(x) \leq 1.95\sqrt{x}$.
-/
theorem theorem_2b {x : ℝ} (hx1 : 1423 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    x - θ x ≤ 1.95 * sqrt x := by sorry

/-- **Buthe Theorem 2(c)**

If $1 \leq x \leq 10^{19}$, then $x - \vartheta(x) > 0.05\sqrt{x}$.
-/
theorem theorem_2c {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    x - θ x ≥ 0.05 * sqrt x := by sorry

/-- **Buthe Theorem 2(d)**

If $2 \leq x \leq 10^{19}$, then $|\li(x) - \pi^*(x)| < \frac{\sqrt{x}}{\log x}$.
-/
theorem theorem_2d {x : ℝ} (hx1 : 2 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    abs (li x - pi_star x) < sqrt x / log x := by sorry

/-- **Buthe Theorem 2(e)**

If $2 \leq x \leq 10^{19}$, then
  $$
  \li(x) - \pi(x) \leq \frac{\sqrt{x}}{\log(x)}\left(1.95 + \frac{3.9}{\log x} + \frac{19.5}{\log(x)^2}\right).
  $$
-/
theorem theorem_2e {x : ℝ} (hx1 : 2 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    li x - pi x ≤ (sqrt x / log x) * (1.95 + 3.9 / log x + 19.5 / (log x) ^ 2) := by
  sorry

/-- **Buthe Theorem 2(f)**

If $2 \leq x \leq 10^{19}$, then $\mathrm{li}(x) - \pi(x) > 0$.
-/
theorem theorem_2f {x : ℝ} (hx1 : 2 ≤ x) (hx2 : x ≤ 10 ^ 19) :
    li x - pi x > 0 := by sorry


end Buthe
