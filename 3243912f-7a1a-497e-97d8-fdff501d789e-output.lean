/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3243912f-7a1a-497e-97d8-fdff501d789e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem pi_error_identity (x : ℝ) (hx : 2 ≤ x) :
    pi x - li x = (θ x - x) / log x + 2 / log 2 + ∫ t in Set.Icc 2 x, (θ t - t) / (t * log t ^ 2)
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

/- **Integral identity for pi - li**

If $x \geq 2$, then
$$\pi(x) - \textrm{li}(x) = \frac{\theta(x) - x}{\log x} + \frac{2}{\log 2} + \int_{2}^{x} \frac{\theta(t) -t}{t \log^{2}t}\, dt.$$

PROVIDED SOLUTION:
Follows from Sublemma \ref{rs-417} and the fundamental theorem of calculus.
-/
noncomputable section AristotleLemmas

/-
Integration by parts formula for Li(x).
-/
open Real Set MeasureTheory intervalIntegral

lemma Li_eq_sub_add_integral (x : ℝ) (hx : 2 ≤ x) :
    Li x = x / log x - 2 / log 2 + ∫ t in Icc 2 x, 1 / log t ^ 2 := by
      rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ( by linarith ) ];
      rw [ Li ];
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      rotate_right;
      use fun t => t / Real.log t + ∫ u in ( 2 : ℝ )..t, 1 / Real.log u ^ 2;
      · norm_num ; ring;
      · intro t ht;
        -- The derivative of the integral term is given by the Fundamental Theorem of Calculus.
        have h_ftc : HasDerivAt (fun t => ∫ u in (2 : ℝ)..t, 1 / Real.log u ^ 2) (1 / Real.log t ^ 2) t := by
          apply_rules [ intervalIntegral.integral_hasDerivAt_right ];
          · apply_rules [ ContinuousOn.intervalIntegrable ];
            exact continuousOn_of_forall_continuousAt fun u hu => ContinuousAt.div continuousAt_const ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hu <;> linarith [ Set.mem_Icc.mp ( by simpa [ hx ] using ht ) ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp hu <;> linarith [ Set.mem_Icc.mp ( by simpa [ hx ] using ht ) ] ) ) ) );
          · exact Measurable.stronglyMeasurable ( by exact Measurable.div measurable_const ( by exact Measurable.pow_const ( Real.measurable_log ) _ ) ) |> fun h => h.stronglyMeasurableAtFilter;
          · exact ContinuousAt.div continuousAt_const ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp ht <;> linarith ) ) ) );
        convert HasDerivAt.add ( HasDerivAt.div ( hasDerivAt_id t ) ( Real.hasDerivAt_log ( show t ≠ 0 by cases Set.mem_uIcc.mp ht <;> linarith ) ) ( ne_of_gt ( Real.log_pos ( show t > 1 by cases Set.mem_uIcc.mp ht <;> linarith ) ) ) ) h_ftc using 1 ; ring;
        by_cases h : t = 0 <;> simp +decide [ sq, mul_assoc, h ];
        by_cases h' : Real.log t = 0 <;> aesop;
      · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const ( Real.continuousAt_log ( by linarith [ Set.mem_Icc.mp ( by simpa [ hx ] using ht ) ] ) ) ( ne_of_gt ( Real.log_pos ( by linarith [ Set.mem_Icc.mp ( by simpa [ hx ] using ht ) ] ) ) ) )

/-
Relationship between pi(x) and theta(x) using partial summation.
-/
open Real Set MeasureTheory intervalIntegral Chebyshev

lemma pi_eq_theta_div_log_add_integral (x : ℝ) (hx : 2 ≤ x) :
    pi x = θ x / log x + ∫ t in Icc 2 x, θ t / (t * log t ^ 2) := by
      -- By definition of $pi$, we know that
      have h_pi_def : _root_.pi x = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), 1 := by
        norm_num +zetaDelta at *;
        unfold _root_.pi;
        rw [ Nat.primeCounting ];
        rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
        congr 2 with ( _ | i ) <;> aesop;
      -- By definition of $theta$, we know that
      have h_theta_def : ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), 1 = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), (Real.log p / Real.log x) + ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), (∫ t in Set.Icc (p : ℝ) x, (1 / (t * (Real.log t) ^ 2) * Real.log p)) := by
        rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl ];
        intro p hp; rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ] <;> norm_num;
        · rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
          rotate_right;
          use fun t => -1 / Real.log t;
          · ring_nf; norm_num [ ne_of_gt, Real.log_pos, show p > 1 from Nat.Prime.one_lt ( Finset.mem_filter.mp hp |>.2 ), show x > 1 from one_lt_two.trans_le hx ] ;
          · intro t ht; convert HasDerivAt.div ( hasDerivAt_const _ _ ) ( Real.hasDerivAt_log ( show t ≠ 0 from by cases Set.mem_uIcc.mp ht <;> linarith [ show ( p : ℝ ) ≥ 1 by norm_cast; linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) ] ] ) ) ( ne_of_gt <| Real.log_pos <| show t > 1 from by cases Set.mem_uIcc.mp ht <;> linarith [ show ( p : ℝ ) ≥ 2 by norm_cast; exact Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ] ) using 1 ; ring;
          · apply_rules [ ContinuousOn.intervalIntegrable ];
            exact continuousOn_of_forall_continuousAt fun y hy => ContinuousAt.mul ( ContinuousAt.inv₀ ( ContinuousAt.pow ( Real.continuousAt_log ( by cases Set.mem_uIcc.mp hy <;> linarith [ show ( p : ℝ ) ≥ 2 by norm_cast; exact Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by cases Set.mem_uIcc.mp hy <;> linarith [ show ( p : ℝ ) ≥ 2 by norm_cast; exact Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ] ) ) ) ) ) ( ContinuousAt.inv₀ ( continuousAt_id ) ( ne_of_gt ( by cases Set.mem_uIcc.mp hy <;> linarith [ show ( p : ℝ ) ≥ 2 by norm_cast; exact Nat.Prime.two_le ( Finset.mem_filter.mp hp |>.2 ) ] ) ) );
        · exact le_trans ( Nat.cast_le.mpr ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ) ) ( Nat.floor_le ( by positivity ) );
      convert h_theta_def using 2;
      · rw [ ← Finset.sum_div ];
        unfold theta; aesop;
      · -- By Fubini's theorem, we can interchange the order of summation and integration.
        have h_fubini : ∫ t in Set.Icc 2 x, (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), (if p ≤ t then Real.log p else 0)) / (t * (Real.log t) ^ 2) = ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), ∫ t in Set.Icc 2 x, (if p ≤ t then Real.log p else 0) / (t * (Real.log t) ^ 2) := by
          rw [ ← MeasureTheory.integral_finset_sum ];
          · simp +decide only [Finset.sum_div];
          · intro p hp; refine' MeasureTheory.Integrable.mono' _ _ _;
            refine' fun t => Real.log p / ( t * Real.log t ^ 2 );
            · exact ContinuousOn.integrableOn_Icc ( continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const ( ContinuousAt.mul continuousAt_id <| ContinuousAt.pow ( Real.continuousAt_log <| by linarith [ ht.1 ] ) _ ) <| ne_of_gt <| mul_pos ( by linarith [ ht.1 ] ) <| sq_pos_of_pos <| Real.log_pos <| by linarith [ ht.1 ] );
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.mul ( Measurable.ite ( measurableSet_Ici ) measurable_const measurable_const ) ( Measurable.inv ( measurable_id'.mul ( Real.measurable_log.pow_const 2 ) ) ) );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with t ht ; split_ifs <;> norm_num [ abs_div, abs_mul, abs_of_nonneg, ht.1.trans' ];
              · rw [ abs_of_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) ) ) ];
              · exact div_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) ) ) ( mul_nonneg ( by linarith [ ht.1 ] ) ( sq_nonneg _ ) );
        convert h_fubini using 1;
        · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t ht => _;
          rw [ Finset.sum_filter ];
          rw [ show θ t = ∑ p ∈ Finset.Icc 1 ⌊t⌋₊, if Nat.Prime p then Real.log p else 0 from ?_ ];
          · rw [ ← Finset.sum_subset ( Finset.Icc_subset_Icc_right ( Nat.floor_mono ht.2 ) ) ];
            · exact congrArg₂ _ ( Finset.sum_congr rfl fun p hp => by split_ifs <;> linarith [ Nat.floor_le ( show 0 ≤ t by linarith [ ht.1 ] ), show ( p : ℝ ) ≤ ⌊t⌋₊ by exact_mod_cast Finset.mem_Icc.mp hp |>.2 ] ) rfl;
            · simp +zetaDelta at *;
              exact fun n hn₁ hn₂ hn₃ hn₄ hn₅ => absurd ( hn₃ hn₁ ) ( not_lt_of_ge ( Nat.le_floor hn₅ ) );
          · rw [ Finset.sum_ite ] ; aesop;
        · refine' Finset.sum_congr rfl fun p hp => _;
          rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
          congr with y ; split_ifs <;> ring;
          · linarith;
          · exact False.elim <| ‹¬ ( 2 ≤ y ∧ y ≤ x ) › ⟨ by linarith [ show ( p : ℝ ) ≥ 2 by exact_mod_cast Nat.Prime.two_le <| Finset.mem_filter.mp hp |>.2 ], by linarith ⟩;
          · aesop

/-
Identity for pi(x) - Li(x).
-/
open Real Set MeasureTheory intervalIntegral Chebyshev

lemma pi_sub_Li_eq (x : ℝ) (hx : 2 ≤ x) :
    pi x - Li x = (θ x - x) / log x + 2 / log 2 + ∫ t in Icc 2 x, (θ t - t) / (t * log t ^ 2) := by
      have h_integral : ∫ t in Set.Icc 2 x, (θ t - t) / (t * Real.log t ^ 2) = (∫ t in Set.Icc 2 x, θ t / (t * Real.log t ^ 2)) - (∫ t in Set.Icc 2 x, 1 / Real.log t ^ 2) := by
        rw [ ← MeasureTheory.integral_sub ];
        · refine' MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t ht => by rw [ sub_div, div_eq_mul_inv ] ; ring_nf; norm_num [ show t ≠ 0 by linarith [ ht.1 ], show Real.log t ≠ 0 by exact ne_of_gt <| Real.log_pos <| by linarith [ ht.1 ] ] ;
        · -- Since θ(t) is bounded by log 4 * t, we have |θ(t) / (t * (log t)^2)| ≤ log 4 / (log t)^2.
          have h_bound : ∀ t ∈ Set.Icc 2 x, |θ t / (t * (Real.log t)^2)| ≤ Real.log 4 / (Real.log t)^2 := by
            intros t ht
            have h_theta_bound : θ t ≤ Real.log 4 * t := by
              exact Chebyshev.theta_le_log4_mul_x ( by linarith [ ht.1 ] );
            rw [ abs_of_nonneg ( div_nonneg ( by exact Finset.sum_nonneg fun _ _ => Real.log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by aesop ) <| mul_nonneg ( by linarith [ ht.1 ] ) <| sq_nonneg _ ), div_le_div_iff₀ ] <;> nlinarith [ ht.1, ht.2, Real.log_pos <| show 1 < t by linarith [ ht.1 ], Real.log_le_sub_one_of_pos <| show 0 < t by linarith [ ht.1 ], show 0 ≤ θ t from Finset.sum_nonneg fun _ _ => Real.log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by aesop ];
          refine' MeasureTheory.Integrable.mono' _ _ _;
          refine' fun t => Real.log 4 / Real.log t ^ 2;
          · exact ContinuousOn.integrableOn_Icc ( continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const ( ContinuousAt.pow ( Real.continuousAt_log ( by linarith [ ht.1 ] ) ) _ ) ( ne_of_gt ( sq_pos_of_pos ( Real.log_pos ( by linarith [ ht.1 ] ) ) ) ) );
          · refine' Measurable.aestronglyMeasurable _;
            refine' Measurable.mul _ _;
            · have h_measurable : Measurable (fun t : ℕ => ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 0 t), Real.log p) := by
                exact?;
              exact h_measurable.comp ( measurable_id'.nat_floor );
            · exact Measurable.inv ( measurable_id.mul ( Real.measurable_log.pow_const 2 ) );
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with t ht using h_bound t ht;
        · exact ContinuousOn.integrableOn_Icc ( continuousOn_const.div ( ContinuousOn.pow ( Real.continuousOn_log.mono <| by norm_num ) _ ) fun t ht => ne_of_gt <| sq_pos_of_pos <| Real.log_pos <| by linarith [ ht.1 ] );
      rw [ h_integral, pi_eq_theta_div_log_add_integral x hx, Li_eq_sub_add_integral x hx ] ; ring

end AristotleLemmas

theorem pi_error_identity (x : ℝ) (hx : 2 ≤ x) :
    pi x - Li x = (θ x - x) / log x + 2 / log 2 + ∫ t in Set.Icc 2 x, (θ t - t) / (t * log t ^ 2) := by
    convert pi_sub_Li_eq x hx using 1

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

/-- **Bound for integral of an inverse power of log**

For $x \geq 2$ we have
$$\int_2^x \frac{dt}{\log^7 t} < \frac{x}{\log^7 x} + 7 \Big( \frac{\sqrt{x}}{\log^8 2} + \frac{2^8 x}{\log^8 x} \Big).$$

PROVIDED SOLUTION:
This follows from the trivial bound $\int_2^x \frac{dt}{\log^7 t} < \int_2^x \frac{dt}{\log^7 \sqrt{x}}$ and the bound $\int_2^x \frac{dt}{\log^7 t} < \int_2^x \frac{dt}{\log^7 x}$.
-/
theorem log_7_int_bound (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 7 < x / log x ^ 7 + 7 * (sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8) := by
    admit

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
