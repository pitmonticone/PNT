/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 756b7e8f-7baf-4f8d-8c2c-24a5a28566fa

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem log_7_int_bound (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 7 < x / log x ^ 7 + 7 * (sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8)
-/

import Mathlib
import PrimeNumberTheoremAnd.DefsAristotle


/-!
# Ramanujan's inequality



Use of prime number theorems to establish Ramanujan's inequality
$$\pi(x)^2 < \frac{e x}{\log x} \pi\Big(\frac{x}{e}\Big)$$
for sufficiently large $x$, following [reference].
-/

namespace Ramanujan

open Real Chebyshev

noncomputable def ε (M x : ℝ) : ℝ := 72 + 2 * M + (2 * M + 132) / log x + (4 * M + 288) / (log x)^2 + (12 * M + 576) / (log x)^3 + (48 * M) / (log x)^4 + (M^2) / (log x)^5

noncomputable def ε' (m x : ℝ) : ℝ := 206 + m + 364 / log x + 381 / (log x)^2 + 238 / (log x)^3 + 97 / (log x)^4 + 30 / (log x)^5 + 8 / (log x)^6

noncomputable def x' (m M x : ℝ) : ℝ := exp (ε M x - ε' m x)

/-- **Criterion for Ramanujan's inequality, substep 1**

Let $M_a \in \mathbb{R}$  and suppose that for $x>x_a$ we have
$$ \pi(x) < x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{M_a x}{\log^6 x}.$$
Then for $x > x_a$ we have
$$ 
\pi^2(x)  <  x^2 \Big\{ \frac{1}{\log^2 x}+ \frac{2}{\log^3 x}+ \frac{5}{\log^4 x}+ \frac{16}{\log^5 x}+ \frac{64}{\log^6 x} + \frac{\epsilon_{M_a}(x)}{\log^7 x} \Big\}
$$
%
where
$$\epsilon_{M_a} (x) = 72 + 2 M_a + \frac{2M_a+132}{\log x} + \frac{4M_a+288}{\log^2 x} + \frac{12 M_a+576}{\log^3 x}+\frac{48M_a}{\log^4 x} + \frac{M_a^2}{\log^5 x}.$$

PROVIDED SOLUTION:
Direct calculation
-/
theorem sq_pi_lt (M_a x_a : ℝ) (hupper : ∀ x > x_a, pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6)) :
    ∀ x > x_a, pi x ^ 2 < x ^ 2 * (∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6) + ε M_a x / log x ^ 7) := by
    admit

/-- **Criterion for Ramanujan's inequality, substep 2**

Let $m_a \in \mathbb{R}$  and suppose that for $x>x_a$ we have
$$\pi(x) > x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{m_a x}{\log^6 x}.$$
Then for $x > e x_a$ we have
$$\frac{ex}{\log x} \pi \Big(\frac{x}{e} \Big) > x^2 \Big\{ \frac{1}{\log^2 x}+ \frac{2}{\log^3 x}+ \frac{5}{\log^4 x}+ \frac{16}{\log^5 x}+ \frac{64}{\log^6 x} + \frac{\epsilon'_{m_a}(x)}{\log^7 x} \Big\},$$
where
$$\epsilon'_{m_a}(x) = 206+m_a+\frac{364}{\log x} + \frac{381}{\log^2 x}+\frac{238}{\log^3 x} + \frac{97}{\log^4 x} + \frac{30}{\log^5 x} + \frac{8}{\log^6 x}.$$

PROVIDED SOLUTION:
We have
$$\frac{ex}{\log x} \pi \Big(\frac{x}{e} \Big) > \frac{x^2}{\log x} \Big( \sum_{k=0}^{4} \frac{k!}{(\log x - 1)^{k+1}}\Big) + \frac{m_a x}{(\log x-1)^{6}}$$
Substituting
\begin{eqnarray*}
\frac{1}{(\log x - 1)^{k+1}} & = & \frac{1}{\log^{k+1} x} \Big(1+ \frac{1}{\log x} + \frac{1}{\log^2 x} + \frac{1}{\log^3 x} + \cdots \Big)^{k+1} \\ \\
& > & \frac{1}{\log^{k+1} x} \Big(1+ \frac{1}{\log x}+ \cdots + \frac{1}{\log^{5-k} x} \Big)^{k+1}
\end{eqnarray*}
we obtain the claim.
-/
theorem ex_pi_gt (m_a x_a : ℝ) (hlower : ∀ x > x_a, x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (m_a * x / log x ^ 6) < pi x) :
    ∀ x > exp 1 * x_a, exp 1 * x / log x * pi (x / exp 1) > x ^ 2 * (∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (m_a * x / log x ^ 6) + ε' m_a x / log x ^ 7) := by
    admit

/-- **Criterion for Ramanujan's inequality**

[reference]
Let $m_a, M_a \in \mathbb{R}$  and suppose that for $x>x_a$ we have

$$ x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+ \frac{m_a x}{\log^6 x} < \pi(x) < x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{M_a x}{\log^6 x}.$$
%
Then Ramanujan's inequality is true if

$$x > \max( e x_{a},x_{a}' )$$
where $x'_a := \exp( \epsilon_{M_a} (x_{a}) - \epsilon'_{m_a} (x_{a}) )$.

PROVIDED SOLUTION:
Combine the previous two sublemmas.
-/
theorem criterion (m_a M_a x_a : ℝ)
  (hlower : ∀ x > x_a, x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (m_a * x / log x ^ 6) < pi x)
  (hupper : ∀ x > x_a, pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6)) :
    ∀ x > max (exp 1 * x_a) (x' m_a M_a x_a), pi x ^ 2 < exp 1 * x / log x * pi (x / exp 1) := by
  admit

/-- **Integral identity for pi - li**

If $x \geq 2$, then
$$\pi(x) - \textrm{li}(x) = \frac{\theta(x) - x}{\log x} + \frac{2}{\log 2} + \int_{2}^{x} \frac{\theta(t) -t}{t \log^{2}t}\, dt.$$

PROVIDED SOLUTION:
Follows from Sublemma \ref{rs-417} and the fundamental theorem of calculus.
-/
theorem pi_error_identity (x : ℝ) (hx : 2 ≤ x) :
    pi x - li x = (θ x - x) / log x + 2 / log 2 + ∫ t in Set.Icc 2 x, (θ t - t) / (t * log t ^ 2) := by
    admit

/-- **Upper bound for pi**

Suppose that for $x \geq 2$ we have $|\theta(x)-x|\log^{5} x\leq x a(x)$. Then
$$
\pi(x)\leq \frac{x}{\log x} +a(x)\frac{x}{\log^6 x}+\int_2^x\frac{d t}{\log^2 t}+\int_2^x\frac{a(t)}{\log^7 t}\ dt.
$$ (cf. [reference])

PROVIDED SOLUTION:
Follows from Lemma \ref{pi-error-identity} and the triangle inequality.
-/
theorem pi_upper (a : ℝ → ℝ) (htheta : ∀ x ≥ 2, abs (θ x - x) * log x ^ 5 ≤ x * a x) (x : ℝ) (hx : 2 ≤ x) :
    pi x ≤ x / log x + a x * x / log x ^ 6 + ∫ t in Set.Icc 2 x, 1 / log t ^ 2 + ∫ t in Set.Icc 2 x, a t / log t ^ 7 := by
    admit

/- **Bound for integral of an inverse power of log**

For $x \geq 2$ we have
$$\int_2^x \frac{dt}{\log^7 t} < \frac{x}{\log^7 x} + 7 \Big( \frac{\sqrt{x}}{\log^8 2} + \frac{2^8 x}{\log^8 x} \Big).$$

PROVIDED SOLUTION:
This follows from the trivial bound $\int_2^x \frac{dt}{\log^7 t} < \int_2^x \frac{dt}{\log^7 \sqrt{x}}$ and the bound $\int_2^x \frac{dt}{\log^7 t} < \int_2^x \frac{dt}{\log^7 x}$.
-/
noncomputable section AristotleLemmas

/-
Integration by parts formula for $\int_2^x \frac{dt}{\log^7 t}$.
-/
theorem log_7_IBP (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 7 = x / log x ^ 7 - 2 / log 2 ^ 7 + 7 * ∫ t in Set.Icc 2 x, 1 / log t ^ 8 := by
      -- Applying integration by parts with $u = (\log t)^{-7}$ and $dv = dt$, we get:
      have h_parts : ∀ a b : ℝ, 2 ≤ a → a ≤ b → ∫ t in a..b, (1 / (Real.log t) ^ 7) = (b / (Real.log b) ^ 7) - (a / (Real.log a) ^ 7) + 7 * ∫ t in a..b, (1 / (Real.log t) ^ 8) := by
        intros a b ha hb
        have h_parts : ∀ t ∈ Set.Icc a b, deriv (fun t => t / (Real.log t) ^ 7) t = 1 / (Real.log t) ^ 7 - 7 * (1 / (Real.log t) ^ 8) := by
          intro t ht; norm_num [ Real.differentiableAt_log, ne_of_gt ( show 0 < Real.log t from Real.log_pos <| by linarith [ ht.1 ] ), ne_of_gt ( show 0 < t from by linarith [ ht.1 ] ) ] ; ring;
          grind;
        have h_parts : ∫ t in a..b, deriv (fun t => t / (Real.log t) ^ 7) t = (b / (Real.log b) ^ 7) - (a / (Real.log a) ^ 7) := by
          rw [ intervalIntegral.integral_deriv_eq_sub' ];
          · rfl;
          · exact fun x hx => DifferentiableAt.div ( differentiableAt_id ) ( DifferentiableAt.pow ( Real.differentiableAt_log ( by cases Set.mem_uIcc.mp hx <;> linarith ) ) _ ) ( pow_ne_zero _ <| ne_of_gt <| Real.log_pos <| by cases Set.mem_uIcc.mp hx <;> linarith );
          · rw [ Set.uIcc_of_le hb ];
            exact ContinuousOn.congr ( by exact ContinuousOn.sub ( continuousOn_const.div ( ContinuousOn.pow ( Real.continuousOn_log.mono <| by intro x hx; exact ne_of_gt <| by linarith [ hx.1 ] ) _ ) fun x hx => pow_ne_zero _ <| ne_of_gt <| Real.log_pos <| by linarith [ hx.1 ] ) <| ContinuousOn.mul continuousOn_const <| continuousOn_const.div ( ContinuousOn.pow ( Real.continuousOn_log.mono <| by intro x hx; exact ne_of_gt <| by linarith [ hx.1 ] ) _ ) fun x hx => pow_ne_zero _ <| ne_of_gt <| Real.log_pos <| by linarith [ hx.1 ] ) h_parts;
        rw [ ← h_parts, intervalIntegral.integral_congr fun t ht => ‹∀ t ∈ Set.Icc a b, deriv ( fun t => t / Real.log t ^ 7 ) t = 1 / Real.log t ^ 7 - 7 * ( 1 / Real.log t ^ 8 ) › t <| by simpa [ hb ] using ht ] ; rw [ intervalIntegral.integral_sub ] <;> norm_num ; ring;
        · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.pow ( ContinuousAt.inv₀ ( Real.continuousAt_log ( by linarith [ Set.mem_Icc.mp ( by simpa [ hb ] using hx ) ] ) ) ( ne_of_gt ( Real.log_pos ( by linarith [ Set.mem_Icc.mp ( by simpa [ hb ] using hx ) ] ) ) ) ) _ ) ..;
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          exact ContinuousOn.mul continuousOn_const <| ContinuousOn.inv₀ ( ContinuousOn.pow ( Real.continuousOn_log.mono <| by intro x hx; cases Set.mem_uIcc.mp hx <;> norm_num <;> linarith ) _ ) fun x hx => ne_of_gt <| pow_pos ( Real.log_pos <| by cases Set.mem_uIcc.mp hx <;> linarith ) _;
      simpa only [ MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hx ] using h_parts 2 x ( by norm_num ) hx

/-
Bound for $\int_2^x \frac{dt}{\log^8 t}$.
-/
theorem log_8_bound (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 8 < sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8 := by
      by_cases h : x < 4;
      · refine' lt_of_le_of_lt ( MeasureTheory.setIntegral_mono_on _ _ measurableSet_Icc fun t ht => one_div_le_one_div_of_le _ <| pow_le_pow_left₀ ( Real.log_nonneg <| by linarith [ ht.1 ] ) ( Real.log_le_log ( by linarith [ ht.1 ] ) ht.1 ) 8 ) _;
        · exact ContinuousOn.integrableOn_Icc ( continuousOn_const.div ( ContinuousOn.pow ( Real.continuousOn_log.mono <| by norm_num ) _ ) fun t ht => pow_ne_zero _ <| ne_of_gt <| Real.log_pos <| by linarith [ ht.1 ] );
        · norm_num;
        · positivity;
        · norm_num [ ← div_eq_mul_inv ];
          exact lt_add_of_le_of_pos ( by gcongr ; cases max_cases ( x - 2 ) 0 <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith ) ] ) ( by exact div_pos ( by positivity ) ( pow_pos ( Real.log_pos ( by linarith ) ) _ ) );
      · -- Split the integral at $\sqrt{x}$.
        have h_split : ∫ t in Set.Icc 2 x, 1 / Real.log t ^ 8 = (∫ t in Set.Icc 2 (Real.sqrt x), 1 / Real.log t ^ 8) + (∫ t in Set.Icc (Real.sqrt x) x, 1 / Real.log t ^ 8) := by
          norm_num [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le, Real.sqrt_le_iff, hx ];
          rw [ ← intervalIntegral.integral_of_le ( by nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith ) ] ), ← intervalIntegral.integral_of_le ( by nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith ) ] ), intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ];
          · exact continuousOn_of_forall_continuousAt fun y hy => ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hy <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith ) ] ) ) _ ) ( pow_ne_zero _ <| ne_of_gt <| Real.log_pos <| by cases Set.mem_uIcc.mp hy <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith ) ] );
          · exact continuousOn_of_forall_continuousAt fun y hy => ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hy <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith ) ] ) ) _ ) ( pow_ne_zero _ <| ne_of_gt <| Real.log_pos <| by cases Set.mem_uIcc.mp hy <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith ) ] );
        -- Bound the first integral.
        have h_first : ∫ t in Set.Icc 2 (Real.sqrt x), 1 / Real.log t ^ 8 ≤ Real.sqrt x / (Real.log 2) ^ 8 := by
          have h_first : ∫ t in Set.Icc 2 (Real.sqrt x), 1 / Real.log t ^ 8 ≤ ∫ t in Set.Icc 2 (Real.sqrt x), 1 / Real.log 2 ^ 8 := by
            refine' MeasureTheory.setIntegral_mono_on _ _ _ _ <;> norm_num;
            · exact ContinuousOn.integrableOn_Icc ( continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by linarith [ ht.1 ] ) ) _ ) ( pow_ne_zero _ ( ne_of_gt ( Real.log_pos ( by linarith [ ht.1 ] ) ) ) ) );
            · exact fun t ht₁ ht₂ => inv_anti₀ ( pow_pos ( Real.log_pos ( by linarith ) ) _ ) ( pow_le_pow_left₀ ( Real.log_nonneg ( by linarith ) ) ( Real.log_le_log ( by linarith ) ( by linarith ) ) _ );
          refine le_trans h_first ?_ ; norm_num;
          rw [ max_eq_left ( sub_nonneg.mpr <| Real.le_sqrt_of_sq_le <| by linarith ) ] ; ring_nf ; norm_num;
          positivity;
        -- Bound the second integral.
        have h_second : ∫ t in Set.Icc (Real.sqrt x) x, 1 / Real.log t ^ 8 ≤ (x - Real.sqrt x) * (2 ^ 8 / (Real.log x) ^ 8) := by
          have h_second : ∀ t ∈ Set.Icc (Real.sqrt x) x, 1 / Real.log t ^ 8 ≤ 2 ^ 8 / (Real.log x) ^ 8 := by
            intros t ht
            have h_log : Real.log t ≥ Real.log (Real.sqrt x) := by
              exact Real.log_le_log ( by positivity ) ht.1;
            rw [ Real.log_sqrt ( by positivity ) ] at h_log;
            rw [ div_le_div_iff₀ ] <;> nlinarith [ pow_pos ( Real.log_pos ( by linarith : 1 < x ) ) 8, pow_le_pow_left₀ ( by linarith [ Real.log_pos ( by linarith : 1 < x ) ] ) h_log 8 ];
          convert MeasureTheory.setIntegral_mono_on _ _ _ h_second <;> norm_num;
          · exact Or.inl <| Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith ⟩;
          · exact ContinuousOn.integrableOn_Icc ( continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by nlinarith [ ht.1, Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith ) ] ) ) _ ) ( pow_ne_zero _ <| ne_of_gt <| Real.log_pos <| by nlinarith [ ht.1, Real.sqrt_nonneg x, Real.sq_sqrt ( show 0 ≤ x by linarith ) ] ) );
        refine' h_split.symm ▸ lt_of_le_of_lt ( add_le_add h_first h_second ) _;
        ring_nf;
        nlinarith [ show 0 < Real.sqrt x * ( Real.log x ) ⁻¹ ^ 8 by exact mul_pos ( Real.sqrt_pos.mpr ( by linarith ) ) ( pow_pos ( inv_pos.mpr ( Real.log_pos ( by linarith ) ) ) _ ) ]

end AristotleLemmas

theorem log_7_int_bound (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 7 < x / log x ^ 7 + 7 * (sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8) := by
    rw [ log_7_IBP x hx ];
    have := log_8_bound x hx;
    linarith [ show 0 ≤ 2 / Real.log 2 ^ 7 by positivity ]

/-- **Lower bound for pi**

Suppose that for $x \geq 2$ we have $|\theta(x)-x|\log^{5} x\leq x a(x)$. Then
$$
\pi(x)\geq \frac{x}{\log x} -a(x)\frac{x}{\log^6 x}+\int_2^x\frac{d t}{\log^2 t}-\int_2^x\frac{a(t)}{\log^7 t}\ dt.
$$ (cf. [reference])

PROVIDED SOLUTION:
Follows from Lemma \ref{pi-error-identity} and the triangle inequality.
-/
theorem pi_lower (a : ℝ → ℝ) (htheta : ∀ x ≥ 2, abs (θ x - x) * log x ^ 5 ≤ x * a x) (x : ℝ) (hx : 2 ≤ x) :
    pi x ≥ x / log x - a x * x / log x ^ 6 + ∫ t in Set.Icc 2 x, 1 / log t ^ 2 - ∫ t in Set.Icc 2 x, a t / log t ^ 7 := by
    admit

/-- **Error estimate for pi, range 1**

For $2 < x \leq 599$ we have
$$E_\pi(x) \leq \frac{2 - \log 2}{2}.$$

PROVIDED SOLUTION:
Trivial.
-/
theorem pi_bound_1 (x : ℝ) (hx : x ∈ Set.Ico 2 599) :
    Eπ x ≤ (2 - log 2) / 2 := by
    admit

/-- **Error estimate for pi, range 2**

For $599 < x \leq \exp(58)$ we have
$$E_\pi(x) \leq \frac{\log^2 x}{8\pi\sqrt{x}}.$$

PROVIDED SOLUTION:
This is [reference].
-/
theorem pi_bound_2 (x : ℝ) (hx : x ∈ Set.Ico 599 (exp 58)) :
    Eπ x ≤ log x ^ 2 / (8 * π * sqrt x) := by
    admit

/-- **Error estimate for pi, range 3**

For $\exp(58) < x < \exp(1169)$ we have
$$E_\pi(x) \leq \sqrt\frac{8}{17\pi}\left(\frac{\log x}{6.455}\right)^{\frac{1}{4}}\exp\left(-\sqrt{\frac{\log x}{6.455}}\right).$$

PROVIDED SOLUTION:
This follows from Corollary \ref{pt_cor_1}.
-/
theorem pi_bound_3 (x : ℝ) (hx : x ∈ Set.Ico (exp 58) (exp 1169)) :
    Eπ x ≤ sqrt (8 / (17 * π)) * (log x / 6.455) ^ (1 / 4) * exp (-sqrt (log x / 6.455)) := by
    admit

/-- **Error estimate for pi, range 4**

For $\exp(1169) \leq x < \exp(2000)$ we have
$$E_\pi(x) \leq 462.0\left(\frac{\log x}{5.573412}\right)^{1.52}\exp\left(-1.89\sqrt{\frac{\log x}{5.573412}}\right).$$

PROVIDED SOLUTION:
This follows from Corollary \ref{pt_cor_1}.
-/
theorem pi_bound_4 (x : ℝ) (hx : x ∈ Set.Ico (exp 1169) (exp 2000)) :
    Eπ x ≤ 462.0 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412)) := by
    admit

/-- **Error estimate for pi, range 5**

For $\exp(2000) \leq x < \exp(3000)$ we have
$$E_\pi(x) \leq 411.5\left(\frac{\log x}{5.573412}\right)^{1.52}\exp\left(-1.89\sqrt{\frac{\log x}{5.573412}}\right).$$

PROVIDED SOLUTION:
This follows from Corollary \ref{pt_cor_1}.
-/
theorem pi_bound_5 (x : ℝ) (hx : x ∈ Set.Ico (exp 2000) (exp 3000)) :
    Eπ x ≤ 411.5 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412)) := by
    admit

noncomputable def a (x : ℝ) : ℝ := (log x)^5 * (
  if x ∈ Set.Ico 2 599 then (2 - log 2) / 2
  else if x ∈ Set.Ico 599 (exp 58) then log x ^ 2 / (8 * π * sqrt x)
  else if x ∈ Set.Ico (exp 58) (exp 1169) then sqrt (8 / (17 * π)) * (log x / 6.455) ^ (1 / 4) * exp (-sqrt (log x / 6.455))
  else if x ∈ Set.Ico (exp 1169) (exp 2000) then 462.0 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412))
  else if x ∈ Set.Ico (exp 2000) (exp 3000) then 411.5 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412))
  else 379.7 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412)))

/-- **Equation (18) of Platt-Trudgian**

For $x \geq 2$ we have
$$E_\pi(x) \leq a(x).$$

PROVIDED SOLUTION:
This follows from the previous five sublemmas.
-/
theorem pi_bound (x : ℝ) (hx : 2 ≤ x) :
    Eπ x ≤ a x := by
    admit

noncomputable def xₐ : ℝ := exp 3914

/-- **Monotonicity of a(x)**

The function $a(x)$ is nonincreasing for $x \geq x_a$.

PROVIDED SOLUTION:
This is a direct calculation.
-/
theorem a_mono : AntitoneOn a (Set.Ici xₐ) := by
    admit

noncomputable def C₁ : ℝ := log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7

noncomputable def C₂ : ℝ := log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 - a t) / log t ^ 7

noncomputable def C₃ : ℝ := 2 * log xₐ ^ 6 / xₐ * ∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1)

noncomputable def Mₐ : ℝ := 120 + a xₐ + C₁ + (720 + a xₐ) * (1 / log xₐ + 7 * 2 ^ 8 / log xₐ ^ 2 + 7 * log xₐ ^ 6 / (sqrt xₐ * log 2 ^ 8))

noncomputable def mₐ : ℝ := 120 - a xₐ - (C₂ + C₃) - a xₐ * (1 / log xₐ + 7 * 2 ^ 8 / log xₐ ^ 2 + 7 * log xₐ ^ 6 / (sqrt xₐ * log 2 ^ 8))

noncomputable def εMₐ : ℝ := 72 + 2 * Mₐ + (2 * Mₐ + 132) / log xₐ + (4 * Mₐ + 288) / log xₐ ^ 2 + (12 * Mₐ + 576) / log xₐ ^ 3 + (48 * Mₐ) / log xₐ ^ 4 + (Mₐ ^ 2) / log xₐ ^ 5

noncomputable def εmₐ : ℝ := 206 + mₐ + 364 / log xₐ + 381 / log xₐ ^ 2 + 238 / log xₐ ^ 3 + 97 / log xₐ ^ 4 + 30 / log xₐ ^ 5 + 8 / log xₐ ^ 6

/-- **Specific upper bound on pi**

For $x \geq x_a$, $$ \pi(x) < x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{M_a x}{\log^6 x}.$$.

PROVIDED SOLUTION:
This follows from the previous lemmas and calculations, including Lemma \ref{log-7-int-bound}.
-/
theorem pi_upper_specific : ∀ x > xₐ, pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (Mₐ * x / log x ^ 6) := by
    admit

/-- **Specific lower bound on pi**

For $x \geq x_a$, $$ \pi(x) > x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}-\frac{m_a x}{\log^6 x}.$$.

PROVIDED SOLUTION:
This follows from the previous lemmas and calculations, including Lemma \ref{log-7-int-bound}.
-/
theorem pi_lower_specific : ∀ x > xₐ, pi x > x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) - (mₐ * x / log x ^ 6) := by
    admit

/-- **Bound for εMₐ - εmₐ**

We have $\epsilon_{M_a} - \epsilon'_{m_a} < 0$.

PROVIDED SOLUTION:
This is a direct calculation.
-/
theorem epsilon_bound : εMₐ - εmₐ < 0 := by
    admit

/-- **Ramanujan's inequality**

For $x \geq e x_a$ we have $\pi(x)^2 < \frac{e x}{\log x} \pi\Big(\frac{x}{e}\Big)$.

PROVIDED SOLUTION:
This follows from the previous lemmas and calculations, including the criterion for Ramanujan's inequality.
-/
theorem ramanujan_final : ∀ x > exp 1 * xₐ, pi x ^ 2 < exp 1 * x / log x * pi (x / exp 1) := by
    admit

end Ramanujan