import Mathlib

open scoped Complex ComplexConjugate

/-!
Already on Mathlib (with a shortened proof):
-/
/-- **hasDerivAt-conj-conj**

Let $f : \mathbb{C} \to \mathbb{C}$ be a complex differentiable function at $p \in \mathbb{C}$
    with derivative $a$. Then the function $g(z) = \overline{f(\overline{z})}$ is complex
    differentiable at $\overline{p}$ with derivative $\overline{a}$.

PROVIDED SOLUTION:
We expand the definition of the derivative and compute.
-/
theorem hasDerivAt_conj_conj {f : ℂ → ℂ} {p a : ℂ} (hf : HasDerivAt f a p) :
    HasDerivAt (fun z ↦ conj (f (conj z))) (conj a) (conj p) := by
  admit

/-!
Submitted to Mathlib:
-/
/-- **deriv-conj-conj**

Let $f : \mathbb{C} \to \mathbb{C}$ be a function at $p \in \mathbb{C}$ with derivative $a$.
    Then the derivative of the function $g(z) = \overline{f(\overline{z})}$ at $\overline{p}$ is
    $\overline{a}$.

PROVIDED SOLUTION:
We proceed by case analysis on whether $f$ is differentiable at $p$. If $f$ is differentiable
    at $p$, then we can apply the previous theorem. If $f$ is not differentiable at $p$, then
    neither is $g$, and both derivatives have the default value of zero.
-/
theorem deriv_conj_conj (f : ℂ → ℂ) (p : ℂ) :
    deriv (fun z ↦ conj (f (conj z))) (conj p) = conj (deriv f p) := by
  admit

/-- **conj-riemannZeta-conj-aux1**

Conjugation symmetry of the Riemann zeta function in the half-plane of convergence. Let
    $s \in \mathbb{C}$ with $\Re(s) > 1$. Then $\overline{\zeta(\overline{s})} = \zeta(s)$.

PROVIDED SOLUTION:
We expand the definition of the Riemann zeta function as a series and find that the two sides
    are equal term by term.
-/
lemma conj_riemannZeta_conj_aux1 (s : ℂ) (hs : 1 < s.re) :
    conj (riemannZeta (conj s)) = riemannZeta s := by
  admit

/-!
% TODO: Submit this and the following corollaries to Mathlib.
-/
/-- **conj-riemannZeta-conj**

Conjugation symmetry of the Riemann zeta function. Let $s \in \mathbb{C}$. Then
    $$\overline{\zeta(\overline{s})} = \zeta(s).$$

PROVIDED SOLUTION:
By the previous lemma, the two sides are equal on the half-plane
    $\{s \in \mathbb{C} : \Re(s) > 1\}$. Then, by analytic continuation, they are equal on the
    whole complex plane.
-/
theorem conj_riemannZeta_conj (s : ℂ) : conj (riemannZeta (conj s)) = riemannZeta s := by
  admit

/-- **riemannZeta-conj**

Conjugation symmetry of the Riemann zeta function. Let $s \in \mathbb{C}$. Then
    $$\zeta(\overline{s}) = \overline{\zeta(s)}.$$

PROVIDED SOLUTION:
This follows as an immediate corollary of Theorem \ref{conj_riemannZeta_conj}.
-/
theorem riemannZeta_conj (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s) := by
  admit

/-- **deriv-riemannZeta-conj**

Conjugation symmetry of the derivative of the Riemann zeta function. Let $s \in \mathbb{C}$.
    Then $$\zeta'(\overline{s}) = \overline{\zeta'(s)}.$$

PROVIDED SOLUTION:
We apply the derivative conjugation symmetry to the Riemann zeta function and use the
    conjugation symmetry of the Riemann zeta function itself.
-/
theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  admit

theorem logDerivZeta_conj (s : ℂ) :
    (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  admit

theorem logDerivZeta_conj' (s : ℂ) :
    (logDeriv riemannZeta) (conj s) = conj (logDeriv riemannZeta s) := by
  admit

/-!
% TODO: Submit this to Mathlib.
-/
/-- **intervalIntegral-conj**

The conjugation symmetry of the interval integral. Let $f : \mathbb{R} \to \mathbb{C}$ be a
    measurable function, and let $a, b \in \mathbb{R}$. Then
    $$\int_{a}^{b} \overline{f(x)} \, dx = \overline{\int_{a}^{b} f(x) \, dx}.$$

PROVIDED SOLUTION:
We unfold the interval integral into an integral over a uIoc and use the conjugation property
    of integrals.
-/
theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  admit