/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 20464ad7-4cca-4015-aab6-32865655bfc5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem F.minus_l1 (lambda y : ℝ) (hlam : lambda ≠ 0) :
    ∫ y : ℝ, I' lambda y - F lambda (-1) y =
      1 / |lambda| - 1 / (rexp (|lambda|) - 1)
-/

import Mathlib
import PrimeNumberTheoremAnd.PrimaryDefinitionsAristotle
import PrimeNumberTheoremAnd.WienerAristotle


/-!
# Chirre-Helfgott's estimates for sums of nonnegative arithmetic functions



We record some estimates from [reference] for summing non-negative functions, with a particular interest in estimating $\psi$.
-/

namespace CH2

/-!
## Fourier-analytic considerations



Some material from [reference], slightly rearranged to take advantage of existing results in the repository.
-/

open Real  MeasureTheory FourierTransform Chebyshev

open ArithmeticFunction hiding log

open Complex hiding log

/-- **CH2 Proposition 2.3, substep 1**

Let $a_n$ be a sequence with $\sum_{n>1} \frac{|a_n|}{n \log^\beta n} < \infty$ for some $\beta > 1$.  Write $G(s)= \sum_n a_n n^{-s} - \frac{1}{s-1}$ for $\mathrm{Re} s > 1$.  Let $\varphi$ be absolutely integrable, supported on $[-1,1]$, and has Fourier decay $\hat \psi(y) = O(1/|y|^\beta)$.  Then for any $x>0$ and $\sigma > 1$
  $$ \frac{1}{2\pi} \sum a_n \frac{x}{n^\sigma} \hat \psi(\frac{T}{2\pi} \log \frac{n}{x} ) = \frac{1}{2\pi T} \int_{-T}^{T} \varphi(\frac{t}{T}) G(\sigma+it) x^{it}\ dt + \int_{-T \log x/2\pi}^\infty e^{-y(\sigma-1)} \hat \varphi(y)\ dy) \frac{x^{2-\sigma}}{T}.$$

PROVIDED SOLUTION:
Use Lemma \ref{first-fourier} and Lemma \ref{second-fourier}, similar to the proof of `limiting\_fourier\_aux`.
-/
theorem prop_2_3_1 {a : ℕ → ℂ} {T β : ℝ} (hT : 0 < T) (hβ : 1 < β)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ}
    (hG' : Set.EqOn G (fun s ↦ ∑' n, a n / n ^ s - 1 / (s - 1)) { z | z.re > 1 })
    {φ : ℝ → ℂ} (hφ_mes : Measurable φ) (hφ_int : Integrable φ)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ x = 0) -- this hypothesis may be unnecessary
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x s : ℝ) (hx : 0 < x) (hs : 1 < s) :
    (1 / (2 * π)) * ∑' (n : ℕ+), a n * (x / (n ^ s : ℝ)) * 𝓕 φ ((T / (2 * π)) * log (n / x)) =
      (1 / (2 * π * T)) *
        ∫ t in Set.Icc (-T) T, φ (t/T) * G (s + t * I) * x ^ (t * I) +
      (∫ y in Set.Iic (-T * log x / (2 * π)), rexp (-y * (s - 1)) * 𝓕 φ y) * (x ^ (2 - s) / T : ℝ) := by
      admit

/-- **CH2 Proposition 2.3**

Let $a_n$ be a sequence with $\sum_{n>1} \frac{|a_n|}{n \log^\beta n} < \infty$ for some $\beta > 1$.  Assume that $\sum_n a_n n^{-s} - \frac{1}{s-1}$ extends continuously to a function $G$ defined on $1 + i[-T,T]$.  Let $\varphi$ be absolutely integrable, supported on $[-1,1]$, and has Fourier decay $\hat \varphi(y) = O(1/|y|^\beta)$.  Then for any $x>0$,
  $$ \frac{1}{2\pi} \sum a_n \frac{x}{n} \hat \varphi(\frac{T}{2\pi} \log \frac{n}{x} ) = \frac{1}{2\pi i T} \int_{1-iT}^{1+iT} \varphi(\frac{s-1}{iT}) G(s) x^{s}\ ds + (\varphi(0) - \int_{-\infty}^{-T \log x/2\pi} \hat \varphi(y)\ dy) \frac{x}{T}.$$

PROVIDED SOLUTION:
Apply Sublemma \ref{ch2-prop-2-3-1} and take the limit as $\sigma \to 1^+$, using the continuity of $G$ and the dominated convergence theorem, as well as the Fourier inversion formula.
-/
theorem prop_2_3 {a : ℕ → ℂ} {T β : ℝ} (hT : 0 < T) (hβ : 1 < β)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ} (hG : ContinuousOn G { z | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T })
    (hG' : Set.EqOn G (fun s ↦ ∑' n, a n / n ^ s - 1 / (s - 1)) { z | z.re > 1 })
    {φ : ℝ → ℂ} (hφ_mes : Measurable φ) (hφ_int : Integrable φ)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ x = 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x : ℝ) (hx : 0 < x) :
    (1 / (2 * π)) * ∑' (n : ℕ+), a n * (x / n) * 𝓕 φ ((T / (2 * π)) * log (n / x)) =
      (1 / (2 * π * T)) *
        ∫ t in Set.Icc (-T) T, φ (t/T) * G (1 + t * I) * x ^ (1 + t * I) +
      (φ 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ y) * (x / T) := by
  admit

/-- **CH2 Definition of $S$, (2.8)**

$S_\sigma(x)$ is equal to $\sum_{n \leq x} a_n / n^\sigma$ if $\sigma < 1$ and $\sum_{n \geq x} a_n / n^\sigma$ if $\sigma > 1$.
-/
noncomputable def S (a : ℕ → ℝ) (s x : ℝ) : ℝ :=
  if s < 1 then ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n / (n ^ s : ℝ)
  else ∑' (n:ℕ), if n ≥ x then a n / (n ^ s : ℝ) else 0

/-- **CH2 Definition of $I$, (2.9)**

$I_\lambda(u) = 1_{[0,\infty)}(\mathrm{sgn}(\lambda)u) e^{-\lambda u}$.
-/
noncomputable def I' (lambda u : ℝ) : ℝ := -- use I' instead of I to avoid clash with Complex.I
  if 0 ≤ lambda * u then exp (-lambda * u) else 0

/-- **CH2 Equation (2.10)**

$S_\sigma(x) = x^{-\sigma} \sum_n a_n \frac{x}{n} I_\lambda( \frac{T}{2\pi} \log \frac{n}{x} )$
  where $\lambda = 2\pi(\sigma-1)/T$.

PROVIDED SOLUTION:
Routine manipulation.
-/
theorem S_eq_I (a : ℕ → ℝ) (s x T : ℝ) (hs : s ≠ 1) (hT : 0 < T)
    : -- may need a summability hypothesis on a
    let lambda := (2 * π * (s - 1)) / T
    S a s x =
      (x ^ (-s):ℝ) * ∑' (n : ℕ+), a n * (x / (n ^ s : ℝ)) * I' lambda ((T / (2 * π)) * log (n / x)) := by
      admit

/-- **CH2 Proposition 2.4, upper bound**

Let $a_n$ be a non-negative sequence with $\sum_{n>1} \frac{|a_n|}{n \log^\beta n} < \infty$ for some $\beta > 1$.  Assume that $\sum_n a_n n^{-s} - \frac{1}{s-1}$ extends continuously to a function $G$ defined on $1 + i[-T,T]$.  Let $\varphi_+$ be absolutely integrable, supported on $[-1,1]$, and has Fourier decay $\hat \varphi_+(y) = O(1/|y|^\beta)$.  Assume $I_\lambda(y) \leq \hat \varphi_+(y)$ for all $y$. Then for any $x\geq 1$ and $\sigma \neq 1$,
  $$ S_\sigma(x) \leq \frac{2\pi x^{1-\sigma}}{T} \varphi_+(0) + \frac{x^{-\sigma}}{T} \int_{-T}^T \varphi_+(t/T) G(1+it) x^{1+it}\ dt - \frac{1_{(-\infty,1)}(\sigma)}{1-\sigma}.$$

PROVIDED SOLUTION:
By the nonnegativity of $a_n$ we have
  $$ S_\sigma(x) \leq x^{-\sigma} \sum_n a_n \frac{x}{n} \hat \varphi_+(\frac{T}{2\pi} \log \frac{n}{x} ).$$
  By Proposition \ref{ch2-prop-2-3} we can express the right-hand side as
  $$ \frac{1}{2\pi i T} \int_{1-iT}^{1+iT} \varphi_+(\frac{s-1}{iT}) G(s) x^{s}\ ds + (\varphi_+(0) - \int_{-\infty}^{-T \log x/2\pi} \hat \varphi_+(y)\ dy) \frac{x}{T}.$$
  If $\lambda > 0$, then $I_\lambda(y)=0$ for negative $y$, so
  $$ -\int_{-\infty}^{-T \log x/2π} \hat \varphi_+(y)\ dy \leq 0.$$
  If $\lambda < 0$, then $I_\lambda(y)=e^{-\lambda y}$ for $y$ negative, so
$$ -\int_{-\infty}^{-T \log x/2π} I_\lambda(y)\ dy \leq e^{\lambda T \log x/2π}/(-\lambda) = x^{\sigma-1}/(-\lambda).$$
hence
$$ -\int_{-\infty}^{-T \log x/2π} \hat \varphi_+(y)\ dy \leq - x^{\sigma-1}/(-\lambda).$$
Since $x^{-\sigma} * (2\pi x / T) * x^{\sigma-1}/(-\lambda) = 1/(1-\sigma)$, the result follows.
-/
theorem prop_2_4_plus {a : ℕ → ℝ} (ha_pos : ∀ n, a n ≥ 0) {T β : ℝ} (hT : 0 < T) (hβ : 1 < β)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ} (hG : ContinuousOn G { z | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T })
    (hG' : Set.EqOn G (fun s ↦ ∑' n, a n / (n ^ s : ℂ) - 1 / (s - 1)) { z | z.re > 1 })
    {φ_plus : ℝ → ℂ} (hφ_mes : Measurable φ_plus) (hφ_int : Integrable φ_plus)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ_plus x = 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ_plus y‖ ≤ C / |y| ^ β)
    (hI_le_Fourier : ∀ y : ℝ, ∀ s : ℝ, s ≠ 1 →
      let lambda := (2 * π * (s - 1)) / T
      I' lambda y ≤ ‖𝓕 φ_plus y‖)
    (x s : ℝ) (hx : 1 ≤ x) (hs : s ≠ 1) :
    S a s x ≤
      ((2 * π * (x ^ (1 - s) : ℝ) / T) * φ_plus 0).re +
      (x ^ (-s) : ℝ) / T *
        (∫ t in Set.Icc (-T) T, φ_plus (t/T) * G (1 + t * I) * (x ^ (1 + t * I))).re -
      if s < 1 then 1 / (1 - s) else 0 := by
  admit

/-- **CH2 Proposition 2.4, lower bound**

Let $a_n$ be a non-negative sequence with $\sum_{n>1} \frac{|a_n|}{n \log^\beta n} < \infty$ for some $\beta > 1$.  Assume that $\sum_n a_n n^{-s} - \frac{1}{s-1}$ extends continuously to a function $G$ defined on $1 + i[-T,T]$.  Let $\varphi_-$ be absolutely integrable, supported on $[-1,1]$, and has Fourier decay $\hat \varphi_-(y) = O(1/|y|^\beta)$.  Assume $\hat \varphi_-(y) \leq I_\lambda(y)$ for all $y$. Then for any $x\geq 1$ and $\sigma \neq 1$,
  $$ S_\sigma(x) \geq \frac{2\pi x^{1-\sigma}}{T} \varphi_-(0) + \frac{x^{-\sigma}}{T} \int_{-T}^T \varphi_-(t/T) G(1+it) x^{1+it}\ dt - \frac{1_{(-\infty,1)}(\sigma)}{1-\sigma}.$$

PROVIDED SOLUTION:
Similar to the proof of Proposition \ref{ch2-prop-2-4-plus}; see [reference] for details.
-/
theorem prop_2_4_minus {a : ℕ → ℝ} (ha_pos : ∀ n, a n ≥ 0) {T β : ℝ} (hT : 0 < T) (hβ : 1 < β)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ} (hG : ContinuousOn G { z | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T })
    (hG' : Set.EqOn G (fun s ↦ ∑' (n : ℕ+), a n / (n ^ s : ℂ) - 1 / (s - 1)) { z | z.re > 1 })
    {φ_minus : ℝ → ℂ} (hφ_mes : Measurable φ_minus) (hφ_int : Integrable φ_minus)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ_minus x = 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ_minus y‖ ≤ C / |y| ^ β)
    (hFourier_le_I : ∀ y : ℝ, ∀ s : ℝ, s ≠ 1 →
      let lambda := (2 * π * (s - 1)) / T
      ‖𝓕 φ_minus y‖ ≤ I' lambda y)
    (x s : ℝ) (hx : 1 ≤ x) (hs : s ≠ 1) :
    S a s x ≥
      ((2 * π * (x ^ (1 - s) : ℝ) / T) * φ_minus 0).re +
      (x ^ (-s) : ℝ) / T *
        (∫ t in Set.Icc (-T) T, φ_minus (t/T) * G (1 + t * I) * (x ^ (1 + t * I))).re -
      if s < 1 then 1 / (1 - s) else 0 := by
  admit

/-!
## Extremal approximants to the truncated exponential



In this section we construct extremal approximants to the truncated exponential function and establish their basic properties, following [reference], although we skip the proof of their extremality.  As such, the material here is organized rather differently from that in the paper.
-/

noncomputable def coth (z : ℂ) : ℂ := 1 / tanh z

/-- **Definition of Phi-circ (4.5)**

$$\Phi^{\pm,\circ}_\nu(z) := \frac{1}{2} (\coth\frac{w}{2} \pm 1)$$
  where $$w = -2\pi i z + \nu.$$
-/
noncomputable def Phi_circ (ν ε : ℝ) (z : ℂ) : ℂ :=
  let w := -2 * π * I * z + (ν : ℂ)
  (1 / 2) * (coth (w / 2) + ε)

/-- **Definition of Phi-star (4.5)**

$$\Phi^{\pm,\ast}_\nu(z) := \frac{i}{2\pi} \left(\frac{\nu}{2} \coth\frac{\nu}{2} - \frac{w}{2} \coth \frac{w}{2} \pm \pi i z\right)$$
  where $$w = -2\pi i z + \nu.$$
-/
noncomputable def Phi_star (ν ε : ℝ) (z : ℂ) : ℂ :=
  let w := -2 * π * I * z + (ν : ℂ)
  (I / (2 * π)) * ((ν / 2) * coth (ν / 2) - (w / 2) * coth (w / 2) + ε * π * I * z)

/-- **Definition of phi-pm (4.5)**

$$\varphi^{\pm}_\nu(t) := 1_{[-1,1]}(t) ( \Phi^{\pm,\circ}_\nu(t) + \mathrm{sgn}(t) \Phi^{\pm,\ast}_\nu(t) ).$$
-/
noncomputable def ϕ_pm (ν ε : ℝ) (t : ℝ) : ℂ :=
  if -1 ≤ t ∧ t ≤ 1 then
    Phi_circ ν ε (t : ℂ) + t.sign * Phi_star ν ε (t : ℂ)
  else 0

/-- **Definition of phi**

$$\varphi_{\pm, \lambda}(t) := \varphi^{\pm}_\nu(\mathrm{sgn}(\lambda) t).$$
-/
noncomputable def ϕ (lambda : ℝ) (ε : ℝ) (t : ℝ) : ℂ :=
  ϕ_pm (|lambda|) ε (lambda.sign * t)

/-- **phi is in L1**

$\varphi_{\pm, \lambda}$ is absolutely integrable.

PROVIDED SOLUTION:
Straightforward estimation
-/
theorem ϕ_integrable (lambda ε : ℝ) (hlam : lambda ≠ 0) : Integrable (ϕ lambda ε) := by
  admit

/-- **phi is absolutely continuous**

$\varphi$ is absolutely continuous.

PROVIDED SOLUTION:
Straightforward estimation
-/
theorem ϕ_continuous (lambda ε : ℝ) (hlam : lambda ≠ 0) : AbsolutelyContinuous (ϕ lambda ε) := by admit

/-- **phi derivative is of bounded variation**

$\varphi'$ is of bounded variation.

PROVIDED SOLUTION:
Straightforward estimation
-/
theorem ϕ_deriv_bv (lambda ε : ℝ) (hlam : lambda ≠ 0) : BoundedVariationOn (deriv (ϕ lambda ε)) Set.univ := by admit

/-- **Definition of F**

$F_{\pm, \lambda}$ is the Fourier transform of $\varphi_{\pm, \lambda}$.
-/
noncomputable def F (lambda : ℝ) (ε : ℝ) (y : ℝ) : ℝ := (𝓕 (ϕ lambda ε) y).re

/-- **F is in L1**

$F$ is absolutely integrable.

PROVIDED SOLUTION:
Use Lemma \ref{decay-alt}.
-/
theorem F_integrable (lambda ε : ℝ) (hlam : lambda ≠ 0) : Integrable (F lambda ε) := by
  admit

lemma Phi_circ_neg_conj (ν ε : ℝ) (s : ℝ) :
    Phi_circ ν ε (-↑s : ℂ) = starRingEnd ℂ (Phi_circ ν ε (↑s : ℂ)) := by
  admit

lemma Phi_star_neg_conj (ν ε : ℝ) (s : ℝ) :
    Phi_star ν ε (-↑s : ℂ) = -starRingEnd ℂ (Phi_star ν ε (↑s : ℂ)) := by
  admit

/-- **F real**

$F_{\pm,\lambda}$ is real-valued.

PROVIDED SOLUTION:
Follows from the symmetry of $\phi$.
-/
theorem F.real (lambda ε y : ℝ) : (𝓕 (ϕ lambda ε) y).im = 0 := by
  admit

/-- **F+ majorizes I**

$F_{+,\lambda}(y) \geq I_\lambda(y)$ for all $y$.

PROVIDED SOLUTION:
TODO.
-/
theorem F.plus_majorizes_I (lambda y : ℝ) (hlam : lambda ≠ 0) :
    F lambda 1 y ≥ I' lambda y := by admit

/-- **F- minorizes I**

$F_{+,\lambda}(y) \geq I_\lambda(y)$ for all $y$.

PROVIDED SOLUTION:
TODO.
-/
theorem F.minus_minorizes_I (lambda y : ℝ) (hlam : lambda ≠ 0) :
    F lambda (-1) y ≤ I' lambda y := by admit

lemma I_prime_integral (lambda : ℝ) (hlam : lambda ≠ 0) :
    ∫ y, I' lambda y = 1 / |lambda| := by
  admit

lemma phi_zero_val (lambda : ℝ) (hlam : lambda ≠ 0) :
    (ϕ lambda 1 0).re = 1 / (1 - Real.exp (-|lambda|)) := by
  admit

lemma I_prime_integrable (lambda : ℝ) (hlam : lambda ≠ 0) :
    MeasureTheory.Integrable (I' lambda) := by
  admit

lemma integral_F_eq_phi_zero (lambda : ℝ) (hlam : lambda ≠ 0) :
    ∫ y, F lambda 1 y = (ϕ lambda 1 0).re := by
  admit

/-- **F+ L1 bound**

$\int (F_{+,\lambda}(y)-I_\lambda(y))\ dy = \frac{1}{1-e^{-|\lambda|}} - \frac{1}{|\lambda|}$. (cf. [reference])

PROVIDED SOLUTION:
This should follow from the Fourier inversion formula, after showing $F_{+,\lambda}$ is in $L^1$..
-/
theorem F.plus_l1 (lambda : ℝ) (hlam : lambda ≠ 0) :
    ∫ y : ℝ, F lambda 1 y - I' lambda y = 1 / (1 - rexp (-|lambda|)) - 1 / |lambda| := by
  admit

/- **F- L1 bound**

$\int (I_\lambda(y) - F_{-,\lambda}(y))\ dy = \frac{1}{|\lambda|} - \frac{1}{e^{|\lambda|} - 1}$. (cf. [reference])

PROVIDED SOLUTION:
This should follow from the Fourier inversion formula, after showing $F_{-,\lambda}$ is in $L^1$..
-/
noncomputable section AristotleLemmas

lemma CH2.phi_minus_zero_val (lambda : ℝ) (hlam : lambda ≠ 0) :
    (CH2.ϕ lambda (-1) 0).re = 1 / (Real.exp (|lambda|) - 1) := by
      unfold CH2.ϕ CH2.ϕ_pm CH2.Phi_circ CH2.Phi_star;
      unfold CH2.coth;
      simp +decide [ Complex.tanh, Complex.exp_re, Complex.exp_im ];
      norm_cast;
      rw [ Real.cosh_eq, Real.sinh_eq ] ; ring;
      norm_num [ Real.exp_neg, Real.exp_mul ];
      field_simp;
      rw [ ← Real.sqrt_eq_rpow, Real.sq_sqrt ( by positivity ) ] ; rw [ div_add', div_eq_div_iff ] <;> nlinarith [ Real.add_one_le_exp |lambda|, abs_pos.mpr hlam ]

#check CH2.ϕ_continuous

lemma CH2.phi_continuous_lemma (lambda ε : ℝ) (hlam : lambda ≠ 0) :
    Continuous (CH2.ϕ lambda ε) := by
      -- The function ϕ is the difference of two absolutely continuous functions, hence it is absolutely continuous.
      have h_abs_cont : AbsolutelyContinuous (CH2.ϕ lambda ε) := by
        exact?;
      refine' continuous_iff_continuousAt.mpr _;
      intro x
      have : ContinuousOn (CH2.ϕ lambda ε) (Set.univ : Set ℝ) := by
        have h_cont : ContinuousOn (CH2.ϕ lambda ε) (Set.univ : Set ℝ) := by
          have := h_abs_cont
          obtain ⟨g, hg⟩ := this;
          refine' Continuous.continuousOn _;
          rw [ show CH2.ϕ lambda ε = fun x => CH2.ϕ lambda ε 0 + ∫ t in ( 0 : ℝ )..x, deriv ( CH2.ϕ lambda ε ) t by ext x; linear_combination hg 0 x ];
          refine' continuous_const.add _;
          apply_rules [ intervalIntegral.continuous_primitive ];
          intro a b;
          rw [ intervalIntegrable_iff ];
          have h_bounded_variation : BoundedVariationOn (deriv (CH2.ϕ lambda ε)) Set.univ := by
            exact?;
          have h_integrable : MeasureTheory.IntegrableOn (deriv (CH2.ϕ lambda ε)) (Set.uIoc a b) := by
            have h_bounded_variation : BoundedVariationOn (deriv (CH2.ϕ lambda ε)) (Set.uIoc a b) := by
              exact h_bounded_variation.mono ( Set.subset_univ _ )
            have h_integrable : MeasureTheory.IntegrableOn (deriv (CH2.ϕ lambda ε)) (Set.uIoc a b) := by
              have h_bounded_variation : BoundedVariationOn (deriv (CH2.ϕ lambda ε)) (Set.uIoc a b) := h_bounded_variation
              have h_measurable : Measurable (deriv (CH2.ϕ lambda ε)) := by
                exact measurable_deriv _
              have h_bounded_variation : ∃ C, ∀ x ∈ Set.uIoc a b, ‖deriv (CH2.ϕ lambda ε) x‖ ≤ C := by
                have h_bounded_variation : ∃ C, ∀ x ∈ Set.uIoc a b, ∀ y ∈ Set.uIoc a b, ‖deriv (CH2.ϕ lambda ε) x - deriv (CH2.ϕ lambda ε) y‖ ≤ C := by
                  exact ⟨ _, fun x hx y hy => h_bounded_variation.dist_le hx hy ⟩;
                obtain ⟨ C, hC ⟩ := h_bounded_variation;
                by_cases h : Set.uIoc a b = ∅;
                · aesop;
                · obtain ⟨ x, hx ⟩ := Set.nonempty_iff_ne_empty.mpr h;
                  exact ⟨ C + ‖deriv ( CH2.ϕ lambda ε ) x‖, fun y hy => by have := hC y hy x hx; exact le_trans ( by simpa using norm_add_le ( deriv ( CH2.ϕ lambda ε ) y - deriv ( CH2.ϕ lambda ε ) x ) ( deriv ( CH2.ϕ lambda ε ) x ) ) ( add_le_add_right this _ ) ⟩;
              refine' MeasureTheory.Integrable.mono' _ _ _;
              use fun x => h_bounded_variation.choose;
              · exact Continuous.integrableOn_Ioc ( by continuity );
              · exact h_measurable.aestronglyMeasurable.restrict;
              · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_uIoc ] with x hx using h_bounded_variation.choose_spec x hx;
            exact h_integrable;
          exact h_integrable;
        exact h_cont.mono ( Set.subset_univ _ )
      exact this.continuousAt (by simp)

lemma CH2.integral_F_minus_eq_phi_minus_zero (lambda : ℝ) (hlam : lambda ≠ 0) :
    ∫ y, CH2.F lambda (-1) y = (CH2.ϕ lambda (-1) 0).re := by
      -- By the Fourier inversion formula, we have that the integral of the Fourier transform of φ minus 1 at 0 is equal to φ minus 1 at 0.
      have h_fourier_inversion : ∫ y, 𝓕 (CH2.ϕ lambda (-1)) y = CH2.ϕ lambda (-1) 0 := by
        have h_fourier_inversion : ∀ f : ℝ → ℂ, Continuous f → MeasureTheory.Integrable f → MeasureTheory.Integrable (𝓕 f) → ∫ y, 𝓕 f y = f 0 := by
          intro f hf hf_int hf_fourier_int
          have h_fourier_inversion : ∀ x, f x = ∫ y, 𝓕 f y * Complex.exp (2 * Real.pi * Complex.I * x * y) := by
            have := @Continuous.fourier_inversion;
            specialize this hf hf_int hf_fourier_int;
            intro x; rw [ ← congr_fun this x ] ; simp +decide [ Real.fourierIntegralInv ] ;
            simp +decide [ VectorFourier.fourierIntegral, mul_assoc, mul_comm, mul_left_comm ];
            simp +decide [ mul_assoc, mul_comm, mul_left_comm, Real.fourierChar, Complex.exp_mul_I ];
            norm_num [ mul_assoc, mul_comm, mul_left_comm, Complex.exp_mul_I, Circle.smul_def ];
          simpa using Eq.symm ( h_fourier_inversion 0 );
        apply h_fourier_inversion;
        · exact?;
        · exact?;
        · refine' MeasureTheory.Integrable.congr _ _;
          exact fun y => CH2.F lambda ( -1 ) y + Complex.I * 0;
          · simpa using CH2.F_integrable _ _ hlam |> fun h => h.ofReal;
          · filter_upwards [ ] with y using by simp +decide [ CH2.F, Complex.ext_iff ] ; linarith [ CH2.F.real lambda ( -1 ) y ] ;
      convert congr_arg Complex.re h_fourier_inversion using 1;
      rw [ ← MeasureTheory.integral_congr_ae ];
      convert integral_re ( show MeasureTheory.Integrable ( fun y => 𝓕 ( CH2.ϕ lambda ( -1 ) ) y ) MeasureTheory.MeasureSpace.volume from ?_ ) using 1;
      · contrapose! h_fourier_inversion;
        rw [ MeasureTheory.integral_undef h_fourier_inversion ] ; norm_num [ CH2.phi_minus_zero_val, hlam ];
        rw [ eq_comm ] ; intro h ; have := CH2.phi_minus_zero_val lambda hlam ; norm_num [ h ] at this;
        linarith [ Real.add_one_le_exp |lambda|, abs_pos.mpr hlam ];
      · filter_upwards [ ] with y using rfl

end AristotleLemmas

theorem F.minus_l1 (lambda y : ℝ) (hlam : lambda ≠ 0) :
    ∫ y : ℝ, I' lambda y - F lambda (-1) y =
      1 / |lambda| - 1 / (rexp (|lambda|) - 1) := by
        rw [ MeasureTheory.integral_sub ];
        · rw [ CH2.integral_F_minus_eq_phi_minus_zero, CH2.I_prime_integral, CH2.phi_minus_zero_val ];
          · assumption;
          · assumption;
          · assumption;
        · exact?;
        · exact?

/-!
TODO: Lemmas 4.2, 4.3, 4.4
-/

/-!
## Contour shifting



TODO: incorporate material from [reference].
-/

/-!
## The main theorem



TODO: incorporate material from [reference].
-/

/-!
## Applications to psi



TODO: incorporate material from [reference] onwards.
-/

/-- **Corollary 1.2, part a**

Assume the Riemann hypothesis holds up to height $T \geq 10^7$. For $x > \max(T,10^9)$,
$$\psi(x) - x \cdot \pi T \coth(\pi T) \leq \pi T^{-1} \cdot x + \frac{1}{2\pi} \log^2(T/(2\pi)) - \frac{1}{6\pi} \log(T/(2\pi)) \sqrt{x},$$

PROVIDED SOLUTION:
TBD.
-/
theorem cor_1_2_a {T x : ℝ} (hT : 1e7 ≤ T) (RH : riemannZeta.RH_up_to T) (hx : max T 1e9 < x) :
    |ψ x - x * π * T * (coth (π * T)).re| ≤
      π * T⁻¹ * x + (1 / (2 * π)) * log (T / (2 * π)) ^ 2 - (1 / (6 * π)) * log (T / (2 * π)) * Real.sqrt x := by admit

/-- **Corollary 1.2, part b**

Assume the Riemann hypothesis holds up to height $T \geq 10^7$. For $x > \max(T,10^9)$,
$$\sum_{n \leq x} \frac{\Lambda(n)}{n} \leq \pi \sqrt{T}^{-1} + \frac{1}{2\pi} \log^2(T/(2\pi)) - \frac{1}{6\pi} \log(T/(2\pi)) \frac{1}{x},$$
where $\gamma = 0.577215...$ is Euler’s constant.

PROVIDED SOLUTION:
TBD.
-/
theorem cor_1_2_b {T x : ℝ} (hT : 1e7 ≤ T) (RH : riemannZeta.RH_up_to T) (hx : max T 1e9 < x) :
    ∑ n ∈ Finset.Iic (⌊x⌋₊), Λ n / n ≤
      π * Real.sqrt T⁻¹ + (1 / (2 * π)) * log (T / (2 * π)) ^ 2 - (1 / (6 * π)) * log (T / (2 * π)) / x := by admit

/-- **Corollary 1.3, part a**

For $x \geq 1$,
$$|\psi(x) - x| \leq \pi \cdot 3 \cdot 10^{-12} \cdot x + 113.67 \sqrt{x},$$
where $\psi(x)$ is the Chebyshev function.

PROVIDED SOLUTION:
TBD.
-/
theorem cor_1_3_a (x : ℝ) (hx : 1 ≤ x) :
    |ψ x - x| ≤ π * 3 * 10 ^ (-12 : ℝ) * x + 113.67 * Real.sqrt x := by admit

/-- **Corollary 1.3, part b**

For $x \geq 1$,
$$ \sum_{n \leq x} \frac{\Lambda(n)}{n} = \log x - \gamma + O^*(\pi \cdot \sqrt{3} \cdot 10^{-12} + 113.67 / x).$$

PROVIDED SOLUTION:
TBD.
-/
theorem cor_1_3_b (x : ℝ) (hx : 1 ≤ x) : ∃ E,
    ∑ n ∈ Finset.Iic (⌊x⌋₊), Λ n / n =
      log x - eulerMascheroniConstant + E ∧ |E| ≤ π * Real.sqrt 3 * 10 ^ (-12 : ℝ) + 113.67 / x := by admit

end CH2