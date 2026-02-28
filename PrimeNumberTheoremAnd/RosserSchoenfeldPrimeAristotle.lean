import Mathlib
import PrimeNumberTheoremAnd.MediumPNTAristotle
import PrimeNumberTheoremAnd.SecondaryDefinitionsAristotle
import PrimeNumberTheoremAnd.RosserSchoenfeldPrime_tablesAristotle

/-!
# The prime number bounds of Rosser and Schoenfeld


-/

/-!
In this section we formalize the prime number bounds of Rosser and Schoenfeld [reference].

TODO: Add more results and proofs here, and reorganize the blueprint
-/

namespace RS_prime

open scoped Topology
open Chebyshev Finset Nat Real MeasureTheory Filter Asymptotics

theorem pntBigO : (θ - id) =O[atTop] fun (x : ℝ) ↦ x / log x ^ 2 := by
  admit

/-- **A medium version of the prime number theorem**

$\vartheta(x) = x + O( x / \log^2 x)$.

PROVIDED SOLUTION:
This in principle follows by establishing an analogue of Theorem \ref{chebyshev-asymptotic}, using mediumPNT in place of weakPNT.
-/
theorem pnt : ∃ C ≥ 0, ∀ x ≥ 2, |θ x - x| ≤ C * x / log x ^ 2 := by
  admit

/-- **The Chebyshev function is Stieltjes**

The function $\vartheta(x) = \sum_{p \leq x} \log p$ defines a Stieltjes function (monotone and right continuous).

PROVIDED SOLUTION:
Trivial
-/
noncomputable def θ.Stieltjes : StieltjesFunction := {
  toFun := θ
  mono' := theta_mono
  right_continuous' := by
    admit
}

lemma theta_succ_sub (k : ℕ) : (θ (k + 1) - θ k) = if Nat.Prime (k + 1) then Real.log (k + 1) else 0  := by
  admit

lemma theta_one : θ 1 = 0 := by
  admit

lemma theta_two : θ 2 = Real.log 2 := by
  admit

lemma leftLim_theta_succ (k : ℕ) : Function.leftLim θ (k + 1) = θ k := by
  admit

theorem summable_pre413 {f : ℝ → ℝ} {s : Set ℝ} (hs : Bornology.IsBounded s) (hs_measureable : MeasurableSet s) :
  Summable fun (n: ℕ) ↦ ∫ (x : ℝ) in n..(n + 1), f x ∂«θ».Stieltjes.measure.restrict s := by
  admit

lemma support_pre413 {f : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x) :
  (Function.support fun (n: ℕ) ↦ ∫ (x : ℝ) in ↑n..↑n + 1, f x ∂«θ».Stieltjes.measure.restrict (Set.Icc 2 x)) ⊆
    (Finset.Ico 1 ⌊x⌋₊) := by
  admit

lemma pre_413_measure_inter {x : ℝ} (hx : 2 ≤ x) (y : Finset.Ico 1 ⌊x⌋₊) :
    «θ».Stieltjes.measure.real (Set.Ioc (↑↑y) (↑↑y + 1) ∩ Set.Icc 2 x) = if Nat.Prime (y + 1) then Real.log (↑y + 1) else 0 := by
  admit

/-- **RS-prime display before (4.13)**

$\sum_{p \leq x} f(p) = \int_{2}^x \frac{f(y)}{\log y}\ d\vartheta(y)$.

PROVIDED SOLUTION:
This follows from the definition of the Stieltjes integral.
-/
theorem pre_413 {f : ℝ → ℝ} {x : ℝ} (hf : ContinuousOn f (Set.Icc 2 (x + 1))) (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), f p =
      ∫ y in Set.Icc 2 x, f y / log y ∂θ.Stieltjes.measure := by
  admit

/-- **RS equation (4.13)**

$\sum_{p \leq x} f(p) = \frac{f(x) \vartheta(x)}{\log x} - \int_2^x \vartheta(y) \frac{d}{dy}( \frac{f(y)}{\log y} )\ dy.$

PROVIDED SOLUTION:
Follows from Sublemma \ref{rs-pre-413} and integration by parts.
-/
theorem eq_413 {f : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x) (hf : DifferentiableOn ℝ f (Set.Icc 2 x)) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), f p = f x * θ x / log x -
      ∫ y in 2..x, θ y * deriv (fun t ↦ f t / log t) y := by
  sorry

/-- **RS equation (4.14)**

$$\sum_{p \leq x} f(p) = \int_2^x \frac{f(y)\ dy}{\log y} + \frac{2 f(2)}{\log 2} $$
  $$ + \frac{f(x) (\vartheta(x) - x)}{\log x} - \int_2^x (\vartheta(y) - y) \frac{d}{dy}( \frac{f(y)}{\log y} )\ dy.$$

PROVIDED SOLUTION:
Follows from Sublemma \ref{rs-413} and integration by parts.
-/
theorem eq_414 {f : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x) (hf : DifferentiableOn ℝ f (Set.Icc 2 x))
    (hd : IntervalIntegrable (fun t => deriv (fun s ↦ f s / log s) t) volume 2 x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), f p =
    (∫ y in 2..x, f y / log y) + 2 * f 2 / Real.log 2 +
    f x * (θ x - x) / log x -
    ∫ y in 2..x, (θ y - y) * deriv (fun s ↦ f s / log s) y := by
  admit

/-- **RS equation (4.16)**

$$L_f := \frac{2f(2)}{\log 2} - \int_2^\infty (\vartheta(y) - y) \frac{d}{dy} (\frac{f(y)}{\log y})\ dy.$$
-/
noncomputable def L (f : ℝ → ℝ) : ℝ :=
    2 * f 2 / Real.log 2 - ∫ y in Set.Ioi 2, (θ y - y) * deriv (fun t ↦ f t / log t) y

open intervalIntegral in
theorem _root_.intervalIntegral.interval_add_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {f : ℝ → E} {μ : Measure ℝ} (ha : IntegrableOn f (Set.Ioi a) μ)
    (hb : IntegrableOn f (Set.Ioi b) μ) :
    ∫ (x : ℝ) in a..b, f x ∂μ + ∫ (x : ℝ) in Set.Ioi b, f x ∂μ
    = ∫ (x : ℝ) in Set.Ioi a, f x ∂μ := by
  admit

theorem intervalIntegrable_inv_log_pow (n : ℕ) (m : ℕ) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    IntegrableOn (fun t ↦ 1 / (t ^ n * Real.log t ^ m)) (Set.Ioc x y) volume := by
  admit

theorem ioiIntegrable_inv_log_pow {n : ℕ} (hn : 1 < n) {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun t ↦ 1 / (t * Real.log t ^ n)) (Set.Ioi x) volume := by
  admit

theorem bound_deriv {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ici 2)) {C : ℝ}
    (hC : ∀ x ∈ Set.Ici 2, |f x| ≤ C / x ∧ |deriv f x| ≤ C / x ^ 2) :
    ∀ᵐ (a : ℝ) ∂volume.restrict (Set.Ioi 2), ‖deriv (fun t ↦ f t / log t) a‖ ≤
    C * (1 / (a ^ 2 * log a) + 1 / (a ^ 2 * log a ^ 2)) := by
  admit

theorem integrableOn_deriv {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ici 2)) {C : ℝ}
    (hC : ∀ x ∈ Set.Ici 2, |f x| ≤ C / x ∧ |deriv f x| ≤ C / x ^ 2) :
    IntegrableOn (fun y ↦ (θ y - y) * deriv (fun t ↦ f t / log t) y) (Set.Ioi 2) volume
    ∧ ∀ x ≥ 2, IntervalIntegrable (fun t ↦ deriv (fun s ↦ f s / Real.log s) t) volume 2 x := by
  admit

/-- **RS equation (4.15)**

$$\sum_{p \leq x} f(p) = \int_2^x \frac{f(y)\ dy}{\log y} + L_f $$
  $$ + \frac{f(x) (\vartheta(x) - x)}{\log x} + \int_x^\infty (\vartheta(y) - y) \frac{d}{dy}( \frac{f(y)}{\log y} )\ dy.$$

PROVIDED SOLUTION:
Follows from Sublemma \ref{rs-414} and Definition \ref{rs-416}.
-/
theorem eq_415 {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ici 2)) {x : ℝ} (hx : 2 ≤ x)
    (hft : IntegrableOn (fun y ↦ (θ y - y) * deriv (fun t ↦ f t / log t) y) (Set.Ioi 2) volume)
    (hfi : IntervalIntegrable (fun t ↦ deriv (fun s ↦ f s / Real.log s) t) volume 2 x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), f p = (∫ y in 2..x, f y / log y) + L f +
    f x * (θ x - x) / log x + ∫ y in Set.Ioi x, (θ y - y) * deriv (fun s ↦ f s / log s) y := by
  admit

/-- **RS equation (4.17)**

$$\pi(x) = \frac{\vartheta(x)}{\log x} + \int_2^x \frac{\vartheta(y)\ dy}{y \log^2 y}.$$

PROVIDED SOLUTION:
Follows from Sublemma \ref{rs-413} applied to $f(t) = 1$.
-/
theorem eq_417 {x : ℝ} (hx : 2 ≤ x) :
    pi x = θ x / log x + ∫ y in 2..x, θ y / (y * log y ^ 2) := by
  admit

/-- **RS equation (4.18)**

$$\sum_{p \leq x} \frac{1}{p} = \frac{\vartheta(x)}{x \log x} + \int_2^x \frac{\vartheta(y) (1 + \log y)\ dy}{y^2 \log^2 y}.$$

PROVIDED SOLUTION:
Follows from Sublemma \ref{rs-413} applied to $f(t) = 1/t$.
-/
theorem eq_418 {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) = θ x / (x * log x) +
    ∫ y in 2..x, θ y * (1 + log y) / (y ^ 2 * log y ^ 2) := by
  admit

theorem ioiIntegral_tendsto_zero {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {μ : Measure ℝ} (a : ℝ) (hfi : IntegrableOn f (Set.Ioi a) μ)
    {l : Filter ι} {b : ι → ℝ} [IsCountablyGenerated l] (hb : Tendsto b l atTop) :
    Tendsto (fun i => ∫ x in Set.Ioi (b i), f x ∂μ) l (𝓝 0) := by
  admit

/-- **Meissel-Mertens constant B**

$B := \lim_{x \to \infty} \left( \sum_{p \leq x} \frac{1}{p} - \log \log x \right)$.
-/
noncomputable def _root_.meisselMertensConstant : ℝ := - log (log 2) + L (fun x => 1 / x)

theorem integrableOn_deriv_inv_div_log : IntegrableOn (fun y ↦ (θ y - y) *
    deriv (fun t ↦ 1 / t / Real.log t) y) (Set.Ioi 2) volume ∧
    ∀ x ≥ 2, IntervalIntegrable (fun t ↦ deriv (fun s ↦ 1 / s / Real.log s) t) volume 2 x := by
  admit

theorem meisselMertensConstant_identity {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) =
    log (log x) + meisselMertensConstant + (θ x - x) / (x * log x) +
    ∫ y in Set.Ioi x, (θ y - y) * deriv (fun s ↦ 1 / s / Real.log s) y := by
  admit

theorem mertens_second_theorem : Filter.atTop.Tendsto (fun x : ℝ ↦
    ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) - log (log x)) (𝓝 meisselMertensConstant) := by
  admit

/-- **RS equation (4.19) and Mertens' second theorem**

$$\sum_{p \leq x} \frac{1}{p} = \log \log x + B + \frac{\vartheta(x) - x}{x \log x} $$
  $$ - \int_2^x \frac{(\vartheta(y)-y) (1 + \log y)\ dy}{y^2 \log^2 y}.$$

PROVIDED SOLUTION:
Follows from Sublemma \ref{rs-413} applied to $f(t) = 1/t$. One can also use this identity to demonstrate convergence of the limit defining $B$.
-/
theorem eq_419 {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) =
    log (log x) + meisselMertensConstant + (θ x - x) / (x * log x)
    - ∫ y in Set.Ioi x, (θ y - y) * (1 + log y) / (y ^ 2 * log y ^ 2) := by
  admit

theorem mertens_second_theorem' :
    ∃ C, ∀ x ≥ 2, |∑ p ∈ filter Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) - log (log x)| ≤ C := by
  admit

/-- **Mertens constant E**

$E := \lim_{x \to \infty} \left( \sum_{p \leq x} \frac{\log p}{p} - \log x \right)$.
-/
noncomputable def _root_.mertensConstant : ℝ := - Real.log 2 + L (fun x => log x / x)

lemma log_div_log_eq {x : ℝ} (hx : 1 < x) : log x / x / log x = x⁻¹ := by
  admit

lemma deriv_eq {x} (hx : 2 ≤ x) : deriv (fun s ↦ Real.log s / s / log s) x = -(x ^ 2)⁻¹ := by
  admit

lemma intervalIntegral_eq {x} (hx : 2 ≤ x) : ∫ (y : ℝ) in 2..x, Real.log y / y / Real.log y =
    ∫ (y : ℝ) in 2..x, 1 / y := by
  admit

theorem integrableOn_deriv_inv : IntegrableOn (fun y ↦ - ((θ y - y) / y ^ 2)) (Set.Ioi 2) volume ∧
    ∀ x ≥ 2, IntervalIntegrable (fun t ↦ -(t ^ 2)⁻¹) volume 2 x := by
  admit

/-- **RS equation (4.19) and Mertens' first theorem**

$$\sum_{p \leq x} \frac{\log p}{p} = \log x + E + \frac{\vartheta(x) - x}{x} $$
  $$ - \int_2^x \frac{(\vartheta(y)-y)\ dy}{y^2}.$$

PROVIDED SOLUTION:
Follows from Sublemma \ref{rs-413} applied to $f(t) = \log t / t$.  Convergence will need Theorem \ref{rs-pnt}.
-/
theorem eq_420 {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), Real.log p / p =
    log x + mertensConstant + (θ x - x) / x - ∫ y in Set.Ioi x, (θ y - y) / (y ^ 2) := by
  admit

theorem mertens_first_theorem : Filter.atTop.Tendsto (fun x : ℝ ↦
    ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), Real.log p / p - log x) (𝓝 mertensConstant) := by
  admit

theorem mertens_first_theorem' :
    ∃ C, ∀ x ≥ 2, |∑ p ∈ filter Prime (Iic ⌊x⌋₊), Real.log p / p - Real.log x| ≤ C := by
  admit

/-- **RS Theorem 12**

We have $\psi(x) < c_0 x$ for all $x>0$.
-/
theorem theorem_12 {x : ℝ} (hx : 0 < x) : ψ x < c₀ * x := by sorry


end RS_prime
