import Mathlib
import PrimeNumberTheoremAnd.PrimaryDefinitionsAristotle
import PrimeNumberTheoremAnd.WienerAristotle

open Real

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
    (x σ : ℝ) (hx : 0 < x) (hσ : 1 < σ) :
    (1 / (2 * π)) * ∑' (n : ℕ+), a n * (x / (n ^ σ : ℝ)) * 𝓕 φ ((T / (2 * π)) * log (n / x)) =
      (1 / (2 * π * T)) *
        ∫ t in Set.Icc (-T) T, φ (t/T) * G (σ + t * I) * x ^ (t * I) +
      (∫ y in Set.Iic (-T * log x / (2 * π)), rexp (-y * (σ - 1)) * 𝓕 φ y) * (x ^ (2 - σ) / T : ℝ) := by
      sorry

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
  sorry

/-- **CH2 Definition of $S$, (2.8)**

$S_\sigma(x)$ is equal to $\sum_{n \leq x} a_n / n^\sigma$ if $\sigma < 1$ and $\sum_{n \geq x} a_n / n^\sigma$ if $\sigma > 1$.
-/
noncomputable def S (a : ℕ → ℝ) (σ x : ℝ) : ℝ :=
  if σ < 1 then ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n / (n ^ σ : ℝ)
  else ∑' (n:ℕ), if n ≥ x then a n / (n ^ σ : ℝ) else 0
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
theorem S_eq_I (a : ℕ → ℝ) (s x T : ℝ) (hs : s ≠ 1) (hT : 0 < T) (hx : 0 < x) :
    let lambda := (2 * π * (s - 1)) / T
    S a s x = (x ^ (-s) : ℝ) * ∑' (n : ℕ+), a n * (x / n) * I' lambda ((T / (2 * π)) * log (n / x)) := by
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
    (hI_le_Fourier : ∀ y : ℝ, ∀ σ : ℝ, σ ≠ 1 →
      let lambda := (2 * π * (σ - 1)) / T
      I' lambda y ≤ ‖𝓕 φ_plus y‖)
    (x σ : ℝ) (hx : 1 ≤ x) (hσ : σ ≠ 1) :
    S a σ x ≤
      ((2 * π * (x ^ (1 - σ) : ℝ) / T) * φ_plus 0).re +
      (x ^ (-σ) : ℝ) / T *
        (∫ t in Set.Icc (-T) T, φ_plus (t/T) * G (1 + t * I) * (x ^ (1 + t * I))).re -
      if σ < 1 then 1 / (1 - σ) else 0 := by
  sorry

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
    (hFourier_le_I : ∀ y : ℝ, ∀ σ : ℝ, σ ≠ 1 →
      let lambda := (2 * π * (σ - 1)) / T
      ‖𝓕 φ_minus y‖ ≤ I' lambda y)
    (x σ : ℝ) (hx : 1 ≤ x) (hσ : σ ≠ 1) :
    S a σ x ≥
      ((2 * π * (x ^ (1 - σ) : ℝ) / T) * φ_minus 0).re +
      (x ^ (-σ) : ℝ) / T *
        (∫ t in Set.Icc (-T) T, φ_minus (t/T) * G (1 + t * I) * (x ^ (1 + t * I))).re -
      if σ < 1 then 1 / (1 - σ) else 0 := by
  sorry



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
theorem ϕ_continuous (lambda ε : ℝ) (hlam : lambda ≠ 0) : AbsolutelyContinuous (ϕ lambda ε) := by sorry

/-- **phi derivative is of bounded variation**

$\varphi'$ is of bounded variation.

PROVIDED SOLUTION:
Straightforward estimation
-/
theorem ϕ_deriv_bv (lambda ε : ℝ) (hlam : lambda ≠ 0) : BoundedVariationOn (deriv (ϕ lambda ε)) Set.univ := by sorry

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
    F lambda 1 y ≥ I' lambda y := by sorry

/-- **F- minorizes I**

$F_{-,\lambda}(y) \geq I_\lambda(y)$ for all $y$.

PROVIDED SOLUTION:
TODO.
-/
theorem F.minus_minorizes_I (lambda y : ℝ) (hlam : lambda ≠ 0) :
    F lambda (-1) y ≤ I' lambda y := by sorry


lemma I_prime_integral (lambda : ℝ) (hlam : lambda ≠ 0) :
    ∫ y, I' lambda y = 1 / |lambda| := by
  admit

lemma phi_zero_val (lambda : ℝ) (hlam : lambda ≠ 0) :
    (ϕ lambda 1 0).re = 1 / (1 - Real.exp (-|lambda|)) := by
  admit

lemma I_prime_integrable (lambda : ℝ) (hlam : lambda ≠ 0) :
    MeasureTheory.Integrable (I' lambda) := by
  admit

lemma phi_continuous_lemma (lambda ε : ℝ) (hlam : lambda ≠ 0) :
    Continuous (ϕ lambda ε) := by
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

lemma phi_minus_zero_val (lambda : ℝ) (hlam : lambda ≠ 0) :
    (ϕ lambda (-1) 0).re = 1 / (Real.exp (|lambda|) - 1) := by
  admit

lemma integral_F_minus_eq_phi_minus_zero (lambda : ℝ) (hlam : lambda ≠ 0) :
    ∫ y, F lambda (-1) y = (ϕ lambda (-1) 0).re := by
  admit

/-- **F- L1 bound**

$\int (I_\lambda(y) - F_{-,\lambda}(y))\ dy = \frac{1}{|\lambda|} - \frac{1}{e^{|\lambda|} - 1}$. (cf. [reference])

PROVIDED SOLUTION:
This should follow from the Fourier inversion formula, after showing $F_{-,\lambda}$ is in $L^1$..
-/
theorem F.minus_l1 (lambda : ℝ) (hlam : lambda ≠ 0) :
    ∫ y : ℝ, I' lambda y - F lambda (-1) y = 1 / |lambda| - 1 / (rexp (|lambda|) - 1) := by
  admit

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
      π * T⁻¹ * x + (1 / (2 * π)) * log (T / (2 * π)) ^ 2 - (1 / (6 * π)) * log (T / (2 * π)) * Real.sqrt x := by sorry

/-- **Corollary 1.2, part b**

Assume the Riemann hypothesis holds up to height $T \geq 10^7$. For $x > \max(T,10^9)$,
$$\sum_{n \leq x} \frac{\Lambda(n)}{n} \leq \pi \sqrt{T}^{-1} + \frac{1}{2\pi} \log^2(T/(2\pi)) - \frac{1}{6\pi} \log(T/(2\pi)) \frac{1}{x},$$
where $\gamma = 0.577215...$ is Euler’s constant.

PROVIDED SOLUTION:
TBD.
-/
theorem cor_1_2_b {T x : ℝ} (hT : 1e7 ≤ T) (RH : riemannZeta.RH_up_to T) (hx : max T 1e9 < x) :
    ∑ n ∈ Finset.Iic (⌊x⌋₊), Λ n / n ≤
      π * Real.sqrt T⁻¹ + (1 / (2 * π)) * log (T / (2 * π)) ^ 2 - (1 / (6 * π)) * log (T / (2 * π)) / x := by sorry

/-- **Corollary 1.3, part a**

For $x \geq 1$,
$$|\psi(x) - x| \leq \pi \cdot 3 \cdot 10^{-12} \cdot x + 113.67 \sqrt{x},$$
where $\psi(x)$ is the Chebyshev function.

PROVIDED SOLUTION:
TBD.
-/
theorem cor_1_3_a (x : ℝ) (hx : 1 ≤ x) :
    |ψ x - x| ≤ π * 3 * 10 ^ (-12 : ℝ) * x + 113.67 * Real.sqrt x := by sorry

/-- **Corollary 1.3, part b**

For $x \geq 1$,
$$ \sum_{n \leq x} \frac{\Lambda(n)}{n} = \log x - \gamma + O^*(\pi \cdot \sqrt{3} \cdot 10^{-12} + 113.67 / x).$$

PROVIDED SOLUTION:
TBD.
-/
theorem cor_1_3_b (x : ℝ) (hx : 1 ≤ x) : ∃ E,
    ∑ n ∈ Finset.Iic (⌊x⌋₊), Λ n / n =
      log x - eulerMascheroniConstant + E ∧ |E| ≤ π * Real.sqrt 3 * 10 ^ (-12 : ℝ) + 113.67 / x := by sorry


end CH2
