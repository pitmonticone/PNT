import Mathlib
import PrimeNumberTheoremAnd.AuxiliaryAristotle
import PrimeNumberTheoremAnd.FourierAristotle
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.BasicAristotle
import PrimeNumberTheoremAnd.ResidueCalcOnRectanglesAristotle

-- set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  admit

lemma one_div_cpow_eq_cpow_neg (x s : ℂ) : 1 / x ^ s = x ^ (-s) := by
  admit

lemma div_rpow_eq_rpow_neg (a x s : ℝ) (hx : 0 ≤ x) : a / x ^ s = a * x ^ (-s) := by
  admit

lemma div_rpow_neg_eq_rpow_div {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (-s) / y ^ (-s) = (y / x) ^ s := by
  admit

lemma div_rpow_eq_rpow_div_neg {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ s / y ^ s = (y / x) ^ (-s) := by
  admit

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

/-!
We record here some prelimiaries about the zeta function and general
holomorphic functions.
-/
/-- **ResidueOfTendsTo**

If a function $f$ is holomorphic in a neighborhood of $p$ and
  $\lim_{s\to p} (s-p)f(s) = A$, then
  $f(s) = \frac{A}{s-p} + O(1)$ near $p$.

PROVIDED SOLUTION:
The function $(s - p)\cdot f(s)$ bounded, so by Theorem
  \ref{existsDifferentiableOn_of_bddAbove}, there is a holomorphic function, $g$, say, so that
  $(s-p)f(s) = g(s)$ in a neighborhood of $s=p$, and $g(p)=A$. Now because $g$ is holomorphic,
  near $s=p$, we have $g(s)=A+O(s-p)$. Then when you divide by $(s-p)$, you get
  $f(s) = A/(s-p) + O(1)$.
-/
theorem ResidueOfTendsTo {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 p)
    (hf : HolomorphicOn f (U \ {p}))
    {A : ℂ}
    (h_limit : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A)) :
    ∃ V ∈ 𝓝 p,
    BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (V \ {p})) := by
  admit

theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  admit

theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ ζ' s := by
  admit

/-- **riemannZetaResidue**

The Riemann zeta function $\zeta(s)$ has a simple pole at $s=1$ with residue $1$. In particular,
  the function $\zeta(s) - \frac{1}{s-1}$ is bounded in a neighborhood of $s=1$.

PROVIDED SOLUTION:
From \texttt{riemannZeta\_residue\_one} (in Mathlib), we know that
  $(s-1)\zeta(s)$ goes to $1$ as $s\to1$. Now apply Theorem \ref{ResidueOfTendsTo}.
  (This can also be done using $\zeta_0$ below, which is expressed as
  $1/(s-1)$ plus things that are holomorphic for $\Re(s)>0$...)
-/
theorem riemannZetaResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (ζ - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  admit

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too
theorem deriv_eqOn_of_eqOn_punctured (f g : ℂ → ℂ) (U : Set ℂ) (p : ℂ)
    (hU_open : IsOpen U)
    (h_eq : EqOn f g (U \ {p})) :
    EqOn (deriv f) (deriv g) (U \ {p}) := by
  admit

/- New two theorems to be proven -/

theorem analytic_deriv_bounded_near_point
    (f : ℂ → ℂ) {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U) (hf : HolomorphicOn f U) :
    (deriv f) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  admit

theorem derivative_const_plus_product {g : ℂ → ℂ} (A p x : ℂ) (hg : DifferentiableAt ℂ g x) :
    deriv ((fun _ ↦ A) + g * fun s ↦ s - p) x = deriv g x * (x - p) + g x := by
  admit

theorem diff_translation (p : ℂ) : deriv (fun x => x - p) = fun _ => 1 := by
  admit

-- Key lemma: derivative of (x - p)⁻¹
lemma deriv_inv_sub {x p : ℂ} (hp : x ≠ p) :
  deriv (fun z => (z - p)⁻¹) x =  -((x - p) ^ 2)⁻¹ := by
  admit

-- Alternative cleaner proof using more direct approach
theorem deriv_f_minus_A_inv_sub_clean (f : ℂ → ℂ) (A x p : ℂ)
    (hf : DifferentiableAt ℂ f x) (hp : x ≠ p) :
    deriv (f  - (fun z ↦ A * (z - p)⁻¹)) x = deriv f x + A * ((x - p) ^ 2)⁻¹ := by
  admit

/-- **nonZeroOfBddAbove**

If a function $f$ has a simple pole at a point $p$ with residue $A \neq 0$, then
  $f$ is nonzero in a punctured neighborhood of $p$.

PROVIDED SOLUTION:
We know that $f(s) = \frac{A}{s-p} + O(1)$ near $p$, so we can write
  $$f(s) = \left(f(s) - \frac{A}{s-p}\right) + \frac{A}{s-p}.$$
  The first term is bounded, say by $M$, and the second term goes to $\infty$ as $s \to p$.
  Therefore, there exists a neighborhood $V$ of $p$ such that for all $s \in V \setminus \{p\}$,
  we have $f(s) \neq 0$.
-/
theorem nonZeroOfBddAbove {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, IsOpen V ∧ ∀ s ∈ V \ {p}, f s ≠ 0 := by
  admit

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

theorem logDerivResidue' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_is_open : IsOpen U)
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  admit

/-- **logDerivResidue**

If $f$ is holomorphic in a neighborhood of $p$, and there is a simple pole at $p$, then $f'/
  f$ has a simple pole at $p$ with residue $-1$:
  $$ \frac{f'(s)}{f(s)} = \frac{-1}{s - p} + O(1).$$

PROVIDED SOLUTION:
Using Theorem \ref{existsDifferentiableOn_of_bddAbove}, there is a function $g$ holomorphic
  near $p$, for which $f(s) = A/(s-p) + g(s) = h(s)/ (s-p)$. Here $h(s):= A + g(s)(s-p)$ which
  is nonzero in a neighborhood of $p$ (since $h$ goes to $A$ which is nonzero).
  Then $f'(s) = (h'(s)(s-p) - h(s))/(s-p)^2$, and we can compute the quotient:
  $$
  \frac{f'(s)}{f(s)}+1/(s-p) = \frac{h'(s)(s-p) - h(s)}{h(s)} \cdot \frac{1}{(s-p)}+1/(s-p)
  =
  \frac{h'(s)}{h(s)}.
  $$
  Since $h$ is nonvanishing near $p$, this remains bounded in a neighborhood of $p$.
-/
theorem logDerivResidue {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  admit

/-- **BddAbove-to-IsBigO**

If $f$ is bounded above in a punctured neighborhood of $p$, then $f$ is $O(1)$ in that
  neighborhood.

PROVIDED SOLUTION:
Elementary.
-/
lemma BddAbove_to_IsBigO {f : ℂ → ℂ} {p : ℂ}
    {U : Set ℂ} (hU : U ∈ 𝓝 p) (bdd : BddAbove (norm ∘ f '' (U \ {p}))) :
    f =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
  admit

theorem logDerivResidue'' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) '' (V \ {p})) := by
  admit

/-!
Let's also record that if a function $f$ has a simple pole at $p$ with residue $A$, and $g$ is
holomorphic near $p$, then the residue of $f \cdot g$ is $A \cdot g(p)$.
-/
/-- **ResidueMult**

If $f$ has a simple pole at $p$ with residue $A$, and $g$ is holomorphic near $p$, then the
  residue of $f \cdot g$ at $p$ is $A \cdot g(p)$. That is, we assume that
  $$
  f(s) = \frac{A}{s - p} + O(1)$$
  near $p$, and that $g$ is holomorphic near $p$. Then
  $$
  f(s) \cdot g(s) = \frac{A \cdot g(p)}{s - p} + O(1).$$

PROVIDED SOLUTION:
Elementary calculation.
  $$
  f(s) * g(s) - \frac{A * g(p)}{s - p} =
  \left(f(s) * g(s) - \frac{A * g(s)}{s - p}\right)
  + \left(\frac{A * g(s) - A * g(p)}{s - p}\right).
  $$
  The first term is $g(s)(f(s) - \frac{A}{s - p})$, which is bounded near $p$ by the assumption
  on $f$
   and the fact that $g$ is holomorphic near $p$.
  The second term is $A$ times the log derivative of $g$ at $p$, which is bounded by the assumption
  that  $g$ is holomorphic.
-/
theorem ResidueMult {f g : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (g_holc : HolomorphicOn g U) (U_in_nhds : U ∈ 𝓝 p) {A : ℂ}
    (f_near_p : (f - (fun s ↦ A * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    (f * g - (fun s ↦ A * g p * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  admit

/-!
As a corollary, the log derivative of the Riemann zeta function has a simple pole at $s=1$:
-/
/-- **riemannZetaLogDerivResidue**

The log derivative of the Riemann zeta function $\zeta(s)$ has a simple pole at $s=1$ with
  residue $-1$: $-\frac{\zeta'(s)}{\zeta(s)} - \frac{1}{s-1} = O(1)$.

PROVIDED SOLUTION:
This follows from Theorem \ref{logDerivResidue} and Theorem \ref{riemannZetaResidue}.
-/
theorem riemannZetaLogDerivResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (-(ζ' / ζ) - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  admit

theorem riemannZetaLogDerivResidueBigO :
    (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
  admit

/-- **riemannZeta0**

For any natural $N\ge1$, we define
  $$
  \zeta_0(N,s) :=
  \sum_{1\le n \le N} \frac1{n^s}
  +
  \frac{- N^{1-s}}{1-s} + \frac{-N^{-s}}{2} + s \int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx
  $$
-/
noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : ζ₀ N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  admit

-- move near `Real.differentiableAt_rpow_const_of_ne`
lemma Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  admit

lemma Complex.one_div_cpow_eq {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  admit

-- No longer used
lemma ContDiffOn.hasDeriv_deriv {φ : ℝ → ℂ} {s : Set ℝ} (φDiff : ContDiffOn ℝ 1 φ s) {x : ℝ}
    (x_in_s : s ∈ nhds x) : HasDerivAt φ (deriv φ x) x := by
  admit

-- No longer used
lemma ContDiffOn.continuousOn_deriv {φ : ℝ → ℂ} {a b : ℝ}
    (φDiff : ContDiffOn ℝ 1 φ (uIoo a b)) :
    ContinuousOn (deriv φ) (uIoo a b) := by
  admit

lemma LinearDerivative_ofReal (x : ℝ) (a b : ℂ) : HasDerivAt (fun (t : ℝ) ↦ a * t + b) a x := by
  admit

lemma sum_eq_int_deriv_aux2 {φ : ℝ → ℂ} {a b : ℝ} (c : ℂ)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∫ (x : ℝ) in a..b, (c - x) * deriv φ x =
      (c - b) * φ b - (c - a) * φ a + ∫ (x : ℝ) in a..b, φ x := by
  admit

lemma integrability_aux₀ {a b : ℝ} :
    ∀ᵐ (x : ℝ) ∂MeasureTheory.Measure.restrict MeasureTheory.volume [[a, b]],
      ‖(⌊x⌋ : ℂ)‖ ≤ max ‖a‖ ‖b‖ + 1 := by
  admit

lemma integrability_aux₁ {a b : ℝ} :
    IntervalIntegrable (fun (x : ℝ) ↦ (⌊x⌋ : ℂ)) MeasureTheory.volume a b := by
  admit

lemma integrability_aux₂ {a b : ℝ} :
    IntervalIntegrable (fun (x : ℝ) ↦ (1 : ℂ) / 2 - x) MeasureTheory.volume a b := by
  admit

lemma integrability_aux {a b : ℝ} :
    IntervalIntegrable (fun (x : ℝ) ↦ (⌊x⌋ : ℂ) + 1 / 2 - x) MeasureTheory.volume a b := by
  admit

lemma Finset_coe_Nat_Int (f : ℤ → ℂ) (m n : ℕ) :
    (∑ x ∈ Finset.Ioc m n, f x) = ∑ x ∈ Finset.Ioc (m : ℤ) n, f x := by
  admit

/-- **sum-eq-int-deriv**

Let $a < b$, and let $\phi$ be continuously differentiable on $[a, b]$.
  Then
  $$
  \sum_{a < n \le b} \phi(n) = \int_a^b \phi(x) \, dx
    + \left(\lfloor b \rfloor + \frac{1}{2} - b\right) \phi(b)
    - \left(\lfloor a \rfloor + \frac{1}{2} - a\right) \phi(a)
    - \int_a^b \left(\lfloor x \rfloor + \frac{1}{2} - x\right) \phi'(x) \, dx.
  $$

PROVIDED SOLUTION:
Specialize Abel summation from Mathlib to the trivial arithmetic function and then manipulate
  integrals.
-/
lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (⌊a⌋ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  admit

lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  admit

lemma neg_s_ne_neg_one {s : ℂ} (s_ne_one : s ≠ 1) : -s ≠ -1 := by
  admit

lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  admit

lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  admit

lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  admit

lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  admit

/-- **ZetaSum-aux1**

Let $0 < a < b$ be natural numbers and $s\in \C$ with $s \ne 1$ and $s \ne 0$.
  Then
  $$
  \sum_{a < n \le b} \frac{1}{n^s} =  \frac{b^{1-s} - a^{1-s}}{1-s} + \frac{b^{-s}-a^{-s}}{2}
    + s \int_a^b \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx.
  $$

PROVIDED SOLUTION:
Apply Lemma \ref{sum_eq_int_deriv} to the function $x \mapsto x^{-s}$.
-/
lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc (a : ℤ) b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  admit

lemma ZetaSum_aux1_1' {a b x : ℝ} (apos : 0 < a) (hx : x ∈ Icc a b) : 0 < x := by
  admit

lemma ZetaSum_aux1_1 {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a, b]]) : 0 < x := by
  admit

lemma ZetaSum_aux1_2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c := by
  admit

lemma ZetaSum_aux1_3a (x : ℝ) : -(1/2) < ⌊ x ⌋ + 1/2 - x := by
  admit

lemma ZetaSum_aux1_3b (x : ℝ) : ⌊x⌋ + 1/2 - x ≤ 1/2 := by
  admit

lemma ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 := by
  admit

lemma ZetaSum_aux1_4' (x : ℝ) (hx : 0 < x) (s : ℂ) :
      ‖(⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1)‖ =
      ‖⌊x⌋ + 1 / 2 - x‖ / x ^ ((s + 1).re) := by
  admit

lemma ZetaSum_aux1_4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re := by
  admit

lemma ZetaSum_aux1_5a {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
  (h : x ∈ Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) := by
  admit

lemma ZetaSum_aux1_5b {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ 1 / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  admit

open MeasureTheory in
lemma measurable_floor_add_half_sub : Measurable fun (u : ℝ) ↦ ↑⌊u⌋ + 1 / 2 - u := by
  admit

open MeasureTheory in
lemma ZetaSum_aux1_5c {a b : ℝ} {s : ℂ} :
    let g : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1);
    AEStronglyMeasurable g
      (Measure.restrict volume (Ι a b)) := by
  admit

lemma ZetaSum_aux1_5d {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  admit

lemma ZetaSum_aux1_5 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤
    ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) := by
  admit

/-- **ZetaBnd-aux1a**

For any $0 < a < b$ and  $s \in \C$ with $\sigma=\Re(s)>0$,
  $$
  \int_a^b \left|\frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx\right|
  \le \frac{a^{-\sigma}-b^{-\sigma}}{\sigma}.
  $$

PROVIDED SOLUTION:
Apply the triangle inequality
  $$
  \left|\int_a^b \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx\right|
  \le \int_a^b \frac{1}{x^{\sigma+1}} \, dx,
  $$
  and evaluate the integral.
-/
lemma ZetaBnd_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  admit

lemma tsum_eq_partial_add_tail {N : ℕ} (f : ℕ → ℂ) (hf : Summable f) :
    ∑' (n : ℕ), f n = (∑ n ∈ Finset.range N, f n) + ∑' (n : ℕ), f (n + N) := by
  admit

lemma Finset.Ioc_eq_Ico (M N : ℕ) : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
  admit

lemma Finset.Ioc_eq_Icc (M N : ℕ) : Finset.Ioc N M = Finset.Icc (N + 1) M := by
  admit

lemma Finset.Icc_eq_Ico (M N : ℕ) : Finset.Icc N M = Finset.Ico N (M + 1) := by
  admit

lemma finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  admit

lemma Complex.cpow_tendsto {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  admit

lemma Complex.cpow_inv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  admit

lemma ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  admit

lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  admit

lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  admit

/-- **ZetaSum-aux2**

Let $N$ be a natural number and $s\in \C$, $\Re(s)>1$.
  Then
  $$
  \sum_{N < n} \frac{1}{n^s} =  \frac{- N^{1-s}}{1-s} + \frac{-N^{-s}}{2}
    + s \int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx.
  $$

PROVIDED SOLUTION:
Apply Lemma \ref{ZetaSum_aux1} with $a=N$ and $b\to \infty$.
-/
lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  admit

open MeasureTheory in
/-- **ZetaBnd-aux1b**

For any $N\ge1$ and $s = \sigma + tI \in \C$, $\sigma > 0$,
  $$
  \left| \int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx \right|
  \le \frac{N^{-\sigma}}{\sigma}.
  $$

PROVIDED SOLUTION:
Apply Lemma \ref{ZetaBnd_aux1a} with $a=N$ and $b\to \infty$.
-/
lemma ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by
  admit

/-- **ZetaBnd-aux1**

For any $N\ge1$ and $s = \sigma + tI \in \C$, $\sigma=\in(0,2], 2 < |t|$,
  $$
  \left| s\int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx \right|
  \le 2 |t| \frac{N^{-\sigma}}{\sigma}.
  $$

PROVIDED SOLUTION:
Apply Lemma \ref{ZetaBnd_aux1b} and estimate $|s|\ll |t|$.
-/
lemma ZetaBnd_aux1 (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (hσ : σ ∈ Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ 2 * |t| * N ^ (-σ) / σ := by
  admit

/-!
Big-Oh version of Lemma \ref{ZetaBnd_aux1}.
-/
/-- **ZetaBnd-aux1p**

For any $N\ge1$ and $s = \sigma + tI \in \C$, $\sigma=\in(0,2], 2 < |t|$,
  $$
  \left| s\int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx \right|
  \ll |t| \frac{N^{-\sigma}}{\sigma}.
  $$

PROVIDED SOLUTION:
Apply Lemma \ref{ZetaBnd_aux1b} and estimate $|s|\ll |t|$.
-/
lemma ZetaBnd_aux1p (N : ℕ) (Npos : 1 ≤ N) {σ : ℝ} (hσ : σ ∈ Ioc 0 2) :
    (fun (t : ℝ) ↦
      ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖)
    =O[Filter.principal {t | 2 ≤ |t|}] fun t ↦ |t| * N ^ (-σ) / σ := by
  admit

lemma isOpen_aux : IsOpen {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  admit

open MeasureTheory in
lemma integrable_log_over_pow {r : ℝ} (rneg : r < 0) {N : ℕ} (Npos : 0 < N) :
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  admit

open MeasureTheory in
lemma integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  admit

open MeasureTheory in
lemma hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  admit

noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))

lemma HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  admit

lemma HasDerivAt_cpow_over_var (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  admit

lemma HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (ζ₀ N) (ζ₀' N s) s := by
  admit

/-- **HolomorphicOn-riemannZeta0**

For any $N\ge1$, the function $\zeta_0(N,s)$ is holomorphic on $\{s\in \C\mid \Re(s)>0 ∧ s \ne 1\}$.

PROVIDED SOLUTION:
The function $\zeta_0(N,s)$ is a finite sum of entire functions, plus an integral
  that's absolutely convergent on $\{s\in \C\mid \Re(s)>0 ∧ s \ne 1\}$ by Lemma \ref{ZetaBnd_aux1b}.
-/
lemma HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (ζ₀ N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} := by
  admit

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`
lemma HolomophicOn_riemannZeta :
    HolomorphicOn ζ {s : ℂ | s ≠ 1} := by
  admit

/-- **isPathConnected-aux**

The set $\{s\in \C\mid \Re(s)>0 ∧ s \ne 1\}$ is path-connected.

PROVIDED SOLUTION:
Construct explicit paths from $2$ to any point, either a line segment or two joined ones.
-/
lemma isPathConnected_aux : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  admit

/-- **Zeta0EqZeta**

For $\Re(s)>0$, $s\ne1$, and for any $N$,
  $$
  \zeta_0(N,s) = \zeta(s).
  $$

PROVIDED SOLUTION:
Use Lemma \ref{ZetaSum_aux2} and the Definition \ref{riemannZeta0}.
-/
lemma Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    ζ₀ N s = riemannZeta s := by
  admit

lemma DerivZeta0EqDerivZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re)
    (s_ne_one : s ≠ 1) :
    deriv (ζ₀ N) s = ζ' s := by
  admit

lemma le_trans₄ {α : Type*} [Preorder α] {a b c d : α} : a ≤ b → b ≤ c → c ≤ d → a ≤ d := by
  admit

lemma lt_trans₄ {α : Type*} [Preorder α] {a b c d : α} : a < b → b < c → c < d → a < d := by
  admit

lemma norm_add₄_le {E : Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) :
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  admit

lemma norm_add₅_le {E : Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) (e : E) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  admit

lemma norm_add₆_le {E : Type*} [SeminormedAddGroup E] (a : E) (b : E) (c : E) (d : E) (e : E)
    (f : E) :
    ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  admit

lemma add_le_add_le_add {α : Type*} [Add α] [Preorder α]
    [CovariantClass α α (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
    [CovariantClass α α (Function.swap fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
    {a b c d e f : α} (h₁ : a ≤ b) (h₂ : c ≤ d) (h₃ : e ≤ f) : a + c + e ≤ b + d + f := by
  admit

lemma add_le_add_le_add_le_add {α : Type*} [Add α] [Preorder α]
    [CovariantClass α α (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
    [CovariantClass α α (Function.swap fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
    {a b c d e f g h : α} (h₁ : a ≤ b) (h₂ : c ≤ d) (h₃ : e ≤ f) (h₄ : g ≤ h) :
    a + c + e + g ≤ b + d + f + h:= by
  admit

lemma mul_le_mul₃ {α : Type*} {a b c d e f : α} [MulZeroClass α] [Preorder α] [PosMulMono α]
    [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (h₃ : e ≤ f) (c0 : 0 ≤ c) (b0 : 0 ≤ b)
    (e0 : 0 ≤ e) : a * c * e ≤ b * d * f := by
  admit

/-- **ZetaBnd-aux2**

Given $n ≤ t$ and $\sigma$ with $1-A/\log t \le \sigma$, we have
  that
  $$
  |n^{-s}| \le n^{-1} e^A.
  $$

PROVIDED SOLUTION:
Use $|n^{-s}| = n^{-\sigma}
  = e^{-\sigma \log n}
  \le
  \exp(-\left(1-\frac{A}{\log t}\right)\log n)
  \le
  n^{-1} e^A$,
  since $n\le t$.
-/
lemma ZetaBnd_aux2 {n : ℕ} {t A σ : ℝ} (Apos : 0 < A) (σpos : 0 < σ) (n_le_t : n ≤ |t|)
    (σ_ge : (1 : ℝ) - A / Real.log |t| ≤ σ) :
    ‖(n : ℂ) ^ (-(σ + t * I))‖ ≤ (n : ℝ)⁻¹ * Real.exp A := by
  admit

lemma logt_gt_one {t : ℝ} (t_ge : 3 ≤ t) : 1 < Real.log t := by
  admit

lemma UpperBnd_aux {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (σ_ge : 1 - A / Real.log |t| ≤ σ) :
    let N := ⌊|t|⌋₊;
    0 < N ∧ N ≤ |t| ∧ 1 < Real.log |t| ∧ 1 - A < σ ∧ 0 < σ ∧ σ + t * I ≠ 1 := by
  admit

lemma UpperBnd_aux2 {A σ t : ℝ} (t_ge : 3 < |t|) (σ_ge : 1 - A / Real.log |t| ≤ σ) :
      |t| ^ (1 - σ) ≤ Real.exp A := by
  admit

lemma riemannZeta0_zero_aux (N : ℕ) (Npos : 0 < N) :
    ∑ x ∈ Finset.Ico 0 N, ((x : ℝ))⁻¹ = ∑ x ∈ Finset.Ico 1 N, ((x : ℝ))⁻¹ := by
  admit

lemma UpperBnd_aux3 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), (n : ℂ) ^ (-(σ + t * I))‖ ≤
      Real.exp A * C * Real.log |t| := by
  admit

lemma Nat.self_div_floor_bound {t : ℝ} (t_ge : 1 ≤ |t|) : let N := ⌊|t|⌋₊;
    (|t| / N) ∈ Icc 1 2 := by
  admit

lemma UpperBnd_aux5 {σ t : ℝ} (t_ge : 3 < |t|) (σ_le : σ ≤ 2) : (|t| / ⌊|t|⌋₊) ^ σ ≤ 4 := by
  admit

lemma UpperBnd_aux6 {σ t : ℝ} (t_ge : 3 < |t|) (hσ : σ ∈ Ioc (1 / 2) 2)
    (neOne : σ + t * I ≠ 1) (Npos : 0 < ⌊|t|⌋₊) (N_le_t : ⌊|t|⌋₊ ≤ |t|) :
    ⌊|t|⌋₊ ^ (1 - σ) / ‖1 - (σ + t * I)‖ ≤ |t| ^ (1 - σ) * 2 ∧
    ⌊|t|⌋₊ ^ (-σ) / 2 ≤ |t| ^ (1 - σ) ∧ ⌊|t|⌋₊ ^ (-σ) / σ ≤ 8 * |t| ^ (-σ) := by
  admit

lemma ZetaUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * (5 + 8 * 2); -- the 2 comes from ZetaBnd_aux1
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ + ‖(N : ℂ) ^ (1 - s) / (1 - s)‖
    + ‖(N : ℂ) ^ (-s) / 2‖
    + ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
    ≤ C * Real.log |t| := by
  admit

/-- **ZetaUpperBnd**

For any $s = \sigma + tI \in \C$, $1/2 \le \sigma\le 2, 3 < |t|$
  and any $0 < A < 1$ sufficiently small, and $1-A/\log |t| \le \sigma$, we have
  $$
  |\zeta(s)| \ll \log t.
  $$

PROVIDED SOLUTION:
First replace $\zeta(s)$ by $\zeta_0(N,s)$ for $N = \lfloor |t| \rfloor$.
  We estimate:
  $$
  |\zeta_0(N,s)| \ll
  \sum_{1\le n \le |t|} |n^{-s}|
  +
  \frac{- |t|^{1-\sigma}}{|1-s|} + \frac{-|t|^{-\sigma}}{2} +
  |t| \cdot |t| ^ {-σ} / σ
  $$
  $$
  \ll
  e^A \sum_{1\le n < |t|} n^{-1}
  +|t|^{1-\sigma}
  $$
  ,
  where we used Lemma \ref{ZetaBnd_aux2} and Lemma \ref{ZetaBnd_aux1}.
  The first term is $\ll \log |t|$.
  For the second term, estimate
  $$
  |t|^{1-\sigma}
  \le |t|^{1-(1-A/\log |t|)}
  = |t|^{A/\log |t|} \ll 1.
  $$
-/
lemma ZetaUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2), ‖ζ (σ + t * I)‖ ≤ C * Real.log |t| := by
  admit

lemma norm_complex_log_ofNat (n : ℕ) : ‖(n : ℂ).log‖ = (n : ℝ).log := by
  admit

lemma Real.log_natCast_monotone : Monotone (fun (n : ℕ) ↦ Real.log n) := by
  admit

lemma Finset.Icc0_eq (N : ℕ) : Finset.Icc 0 N = {0} ∪ Finset.Icc 1 N := by
  admit

lemma harmonic_eq_sum_Icc0_aux (N : ℕ) :
    ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = ∑ i ∈ Finset.Icc 1 N, (i : ℝ)⁻¹ := by
  admit

lemma harmonic_eq_sum_Icc0 (N : ℕ) : ∑ i ∈ Finset.Icc 0 N, (i : ℝ)⁻¹ = (harmonic N : ℝ) := by
  admit

lemma DerivUpperBnd_aux1 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖
      ≤ Real.exp A * C * (Real.log |t|) ^ 2 := by
  admit

lemma DerivUpperBnd_aux2 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 →
    1 / 2 < σ → ‖-↑N ^ (1 - s) / (1 - s) ^ 2‖ ≤ A.exp * 2 * (1 / 3) := by
  admit

theorem DerivUpperBnd_aux3 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * ↑N ^ (1 - s) / (1 - s)‖ ≤ A.exp * 2 * |t|.log := by
  admit

theorem DerivUpperBnd_aux4 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * (N : ℂ) ^ (-s) / 2‖ ≤ A.exp * |t|.log := by
  admit

theorem DerivUpperBnd_aux5 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → 1 / 2 < σ →
    ‖1 * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1)‖ ≤
    1 / 3 * (2 * |t| * ↑N ^ (-σ) / σ) := by
  admit

theorem DerivUpperBnd_aux6 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    0 < N → ↑N ≤ |t| → ↑σ + ↑t * I ≠ 1 → 1 / 2 < σ →
    2 * |t| * ↑N ^ (-σ) / σ ≤ 2 * (8 * A.exp) := by
  admit

lemma DerivUpperBnd_aux7_1 {x σ t : ℝ} (hx : 1 ≤ x) :
    let s := ↑σ + ↑t * I;
    ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ = |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
  admit

lemma DerivUpperBnd_aux7_2 {x σ : ℝ} (hx : 1 ≤ x) :
    |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log ≤ x ^ (-σ - 1) * x.log := by
  admit

lemma DerivUpperBnd_aux7_3 {x σ : ℝ} (xpos : 0 < x) (σnz : σ ≠ 0) :
    HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  admit

lemma DerivUpperBnd_aux7_3' {a σ : ℝ} (apos : 0 < a) (σnz : σ ≠ 0) :
    ∀ x ∈ Ici a, HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  admit

lemma DerivUpperBnd_aux7_nonneg {a σ : ℝ} (ha : 1 ≤ a) :
    ∀ x ∈ Ioi a, 0 ≤ x ^ (-σ - 1) * Real.log x := by
  admit

lemma DerivUpperBnd_aux7_tendsto {σ : ℝ} (σpos : 0 < σ) :
    Tendsto (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t)) atTop (nhds 0) := by
  admit

open MeasureTheory in
lemma DerivUpperBnd_aux7_4 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ x ^ (-σ - 1) * Real.log x) (Ioi a) volume := by
  admit

open MeasureTheory in
lemma DerivUpperBnd_aux7_5 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ |(↑⌊x⌋ + (1 : ℝ) / 2 - x)| * x ^ (-σ - 1) * Real.log x)
      (Ioi a) volume := by
  admit

open MeasureTheory in
lemma DerivUpperBnd_aux7_integral_eq {a σ : ℝ} (ha : 1 ≤ a) (σpos : 0 < σ) :
    ∫ (x : ℝ) in Ioi a, x ^ (-σ - 1) * Real.log x =
      1 / σ^2 * a ^ (-σ) + 1 / σ * a ^ (-σ) * Real.log a := by
  admit

open MeasureTheory in
/-- **DerivUpperBnd-aux7**

For any $s = \sigma + tI \in \C$, $1/2 \le \sigma\le 2, 3 < |t|$, and any $0 < A < 1$
  sufficiently small, and $1-A/\log |t| \le \sigma$, we have
  $$
  \left\|s \cdot \int_{N}^{\infty}
    \left(\left\lfloor x \right\rfloor + \frac{1}{2} - x\right) \cdot x^{-s-1} \cdot (-\log x)
  \right\|
  \le 2 \cdot |t| \cdot N^{-\sigma} / \sigma \cdot \log |t|.
  $$

PROVIDED SOLUTION:
Estimate $|s|= |\sigma + tI|$ by $|s|\le 2 +|t| \le 2|t|$ (since $|t|>3$).
  Estimating $|\left\lfloor x \right\rfloor+1/2-x|$ by $1$,
  and using $|x^{-s-1}| = x^{-\sigma-1}$, we have
  $$
  \left\| s \cdot \int_{N}^{\infty}
    \left(\left\lfloor x \right\rfloor + \frac{1}{2} - x\right) \cdot x^{-s-1} \cdot (-\log x)
  \right\|
  \le 2 \cdot |t|
  \int_{N}^{\infty} x^{-\sigma} \cdot (\log x).
  $$
  For the last integral, integrate by parts, getting:
  $$
  \int_{N}^{\infty} x^{-\sigma-1} \cdot (\log x) =
  \frac{1}{\sigma}N^{-\sigma} \cdot \log N + \frac1{\sigma^2} \cdot N^{-\sigma}.
  $$
  Now use $\log N \le \log |t|$ to get the result.
-/
theorem DerivUpperBnd_aux7 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ ≤
      6 * |t| * ↑N ^ (-σ) / σ * |t|.log := by
  admit

lemma ZetaDerivUpperBnd' {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * 59;
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * (Real.log n)‖ +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖
        ≤ C * Real.log |t| ^ 2 := by
  admit

/-- **ZetaDerivUpperBnd**

For any $s = \sigma + tI \in \C$, $1/2 \le \sigma\le 2, 3 < |t|$,
  there is an $A>0$ so that for $1-A/\log t \le \sigma$, we have
  $$
  |\zeta'(s)| \ll \log^2 t.
  $$

PROVIDED SOLUTION:
First replace $\zeta(s)$ by $\zeta_0(N,s)$ for $N = \lfloor |t| \rfloor$.
  Differentiating term by term, we get:
  $$
  \zeta'(s) = -\sum_{1\le n < N} n^{-s} \log n
  + \frac{N^{1 - s}}{(1 - s)^2} + \frac{N^{1 - s} \log N} {1 - s}
  + \frac{N^{-s}\log N}{2} +
  \int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx
  -s \int_N^\infty \log x \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}} \, dx
  .
  $$
  Estimate as before, with an extra factor of $\log |t|$.
-/
lemma ZetaDerivUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2),
    ‖ζ' (σ + t * I)‖ ≤ C * Real.log |t| ^ 2 := by
  admit

lemma Tendsto_nhdsWithin_punctured_map_add {f : ℝ → ℝ} (a x : ℝ)
    (f_mono : StrictMono f) (f_iso : Isometry f) :
    Tendsto (fun y ↦ f y + a) (𝓝[>] x) (𝓝[>] (f x + a)) := by
  admit

lemma Tendsto_nhdsWithin_punctured_add (a x : ℝ) :
    Tendsto (fun y ↦ y + a) (𝓝[>] x) (𝓝[>] (x + a)) := by
  admit

lemma riemannZeta_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ ζ (1 + x)) =O[𝓝[>] 0] (fun x ↦ (1 : ℂ) / x) := by
  admit

/-- **ZetaNear1BndFilter**

As $\sigma\to1^+$,
  $$
  |\zeta(\sigma)| \ll 1/(\sigma-1).
  $$

PROVIDED SOLUTION:
Zeta has a simple pole at $s=1$. Equivalently, $\zeta(s)(s-1)$ remains bounded near $1$.
  Lots of ways to prove this.
  Probably the easiest one: use the expression for $\zeta_0 (N,s)$ with $N=1$ (the term $N^{1-s}/(1-s)$ being the only unbounded one).
-/
lemma ZetaNear1BndFilter :
    (fun σ : ℝ ↦ ζ σ) =O[𝓝[>](1 : ℝ)] (fun σ ↦ (1 : ℂ) / (σ - 1)) := by
  admit

/-- **ZetaNear1BndExact**

There exists a $c>0$ such that for all $1 < \sigma ≤ 2$,
  $$
  |\zeta(\sigma)| ≤ c/(\sigma-1).
  $$

PROVIDED SOLUTION:
Split into two cases, use Lemma \ref{ZetaNear1BndFilter} for $\sigma$ sufficiently small
  and continuity on a compact interval otherwise.
-/
lemma ZetaNear1BndExact :
    ∃ (c : ℝ) (_ : 0 < c), ∀ (σ : ℝ) (_ : σ ∈ Ioc 1 2), ‖ζ σ‖ ≤ c / (σ - 1) := by
  admit

/-- For positive `x` and nonzero `y` we have that
$|\zeta(x)^3 \cdot \zeta(x+iy)^4 \cdot \zeta(x+2iy)| \ge 1$. -/
lemma norm_zeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖ζ (1 + x) ^ 3 * ζ (1 + x + I * y) ^ 4 * ζ (1 + x + 2 * I * y)‖ ≥ 1 := by
  admit

theorem ZetaLowerBound1_aux1 {σ t : ℝ} (this : 1 ≤ ‖ζ σ‖ ^ (3 : ℝ) * ‖ζ (σ + I * t)‖ ^ (4 : ℝ) * ‖ζ (σ + 2 * I * t)‖) :
  ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖ ≥ 1 := by
  admit

lemma ZetaLowerBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖ ≥ 1 := by
  admit

lemma ZetaLowerBound2 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / (‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4)) ≤ ‖ζ (σ + t * I)‖ := by
  admit

theorem ZetaLowerBound3_aux1 (A : ℝ) (ha : A ∈ Ioc 0 (1 / 2)) (t : ℝ)
  (ht_2 : 3 < |2 * t|) : 0 < A / Real.log |2 * t| := by
  admit

theorem ZetaLowerBound3_aux2 {C : ℝ}
  {σ t : ℝ}
  (ζ_2t_bound : ‖ζ (σ + (2 * t) * I)‖ ≤ C * Real.log |2 * t|) :
  ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) ≤ (C * Real.log |2 * t|) ^ ((1 : ℝ) / 4) := by
  admit

theorem ZetaLowerBound3_aux3 (C : ℝ) (c_near : ℝ) {σ : ℝ} (t : ℝ) (σ_gt : 1 < σ) :
  c_near ^ ((3 : ℝ) / 4) * ((-1 + σ) ^ ((3 : ℝ) / 4))⁻¹ * C ^ ((1 : ℝ) / 4) * Real.log |t * 2| ^ ((1 : ℝ) / 4) =
    c_near ^ ((3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * Real.log |t * 2| ^ ((1 : ℝ) / 4) * (-1 + σ) ^ (-(3 : ℝ) / 4) := by
  admit

theorem ZetaLowerBound3_aux4 (C : ℝ) (hC : 0 < C)
  (c_near : ℝ) (hc_near : 0 < c_near) {σ : ℝ} (t : ℝ) (ht : 3 < |t|)
  (σ_gt : 1 < σ)
   :
  0 < c_near ^ ((3 : ℝ) / 4) * (σ - 1) ^ (-(3 : ℝ) / 4) * C ^ ((1 : ℝ) / 4) * Real.log |2 * t| ^ ((1 : ℝ) / 4) := by
  admit

theorem ZetaLowerBound3_aux5
  {σ : ℝ} (t : ℝ)
  (this : ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) * ‖ζ (σ + t * I)‖ ≥ 1) :
  0 < ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
  admit

/-- **ZetaLowerBound3**

There exists a $c>0$ such that for all $1 < \sigma <= 2$ and $3 < |t|$,
  $$
  c \frac{(\sigma-1)^{3/4}}{(\log |t|)^{1/4}} \le |\zeta(\sigma + tI)|.
  $$

PROVIDED SOLUTION:
Combine Lemma \ref{ZetaLowerBound2} with upper bounds for
  $|\zeta(\sigma)|$ (from Lemma \ref{ZetaNear1BndExact}) and
  $|\zeta(\sigma+2it)|$ (from Lemma \ref{ZetaUpperBnd}).
-/
lemma ZetaLowerBound3 :
    ∃ c > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    c * (σ - 1) ^ ((3 : ℝ) / 4) / (Real.log |t|) ^ ((1 : ℝ) / 4) ≤ ‖ζ (σ + t * I)‖ := by
  admit

/-- **ZetaInvBound1**

For all $\sigma>1$,
  $$
  1/|\zeta(\sigma+it)| \le |\zeta(\sigma)|^{3/4}|\zeta(\sigma+2it)|^{1/4}
  $$

PROVIDED SOLUTION:
The identity
  $$
  1 \le |\zeta(\sigma)|^3 |\zeta(\sigma+it)|^4 |\zeta(\sigma+2it)|
  $$
  for $\sigma>1$
  is already proved by Michael Stoll in the EulerProducts PNT file.
-/
lemma ZetaInvBound1 {σ t : ℝ} (σ_gt : 1 < σ) :
    1 / ‖ζ (σ + t * I)‖ ≤ ‖ζ σ‖ ^ ((3 : ℝ) / 4) * ‖ζ (σ + 2 * t * I)‖ ^ ((1 : ℝ) / 4) := by
  admit

lemma Ioi_union_Iio_mem_cocompact {a : ℝ} (ha : 0 ≤ a) : Ioi (a : ℝ) ∪ Iio (-a : ℝ) ∈ cocompact ℝ := by
  admit

lemma lt_abs_mem_cocompact {a : ℝ} (ha : 0 ≤ a) : {t | a < |t|} ∈ cocompact ℝ := by
  admit

/-- **ZetaInvBound2**

For $\sigma>1$ (and $\sigma \le 2$),
  $$
  1/|\zeta(\sigma+it)| \ll (\sigma-1)^{-3/4}(\log |t|)^{1/4},
  $$
  as $|t|\to\infty$.

PROVIDED SOLUTION:
Combine Lemma \ref{ZetaInvBound1} with the bounds in Lemmata \ref{ZetaNear1BndExact} and
  \ref{ZetaUpperBnd}.
-/
lemma ZetaInvBound2 :
    ∃ C > 0, ∀ {σ : ℝ} (_ : σ ∈ Ioc 1 2) (t : ℝ) (_ : 3 < |t|),
    1 / ‖ζ (σ + t * I)‖ ≤ C * (σ - 1) ^ (-(3 : ℝ) / 4) * (Real.log |t|) ^ ((1 : ℝ) / 4) := by
  admit

lemma deriv_fun_re {t : ℝ} {f : ℂ → ℂ} (diff : ∀ (σ : ℝ), DifferentiableAt ℂ f (↑σ + ↑t * I)) :
    (deriv fun {σ₂ : ℝ} ↦ f (σ₂ + t * I)) = fun (σ : ℝ) ↦ deriv f (σ + t * I) := by
  admit

/-- **Zeta-eq-int-derivZeta**

For any $t\ne0$ (so we don't pass through the pole), and $\sigma_1 < \sigma_2$,
  $$
  \int_{\sigma_1}^{\sigma_2}\zeta'(\sigma + it) dt =
  \zeta(\sigma_2+it) - \zeta(\sigma_1+it).
  $$

PROVIDED SOLUTION:
This is the fundamental theorem of calculus.
-/
lemma Zeta_eq_int_derivZeta {σ₁ σ₂ t : ℝ} (t_ne_zero : t ≠ 0) :
    (∫ σ in σ₁..σ₂, ζ' (σ + t * I)) = ζ (σ₂ + t * I) - ζ (σ₁ + t * I) := by
  admit

/-- **Zeta-diff-Bnd**

For any $A>0$ sufficiently small, there is a constant $C>0$ so that
  whenever $1- A / \log t \le \sigma_1 < \sigma_2\le 2$ and $3 < |t|$, we have that:
  $$
  |\zeta (\sigma_2 + it) - \zeta (\sigma_1 + it)|
  \le C (\log |t|)^2 (\sigma_2 - \sigma_1).
  $$

PROVIDED SOLUTION:
Use Lemma \ref{Zeta_eq_int_derivZeta} and
  estimate trivially using Lemma \ref{ZetaDerivUpperBnd}.
-/
lemma Zeta_diff_Bnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ₁ σ₂ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : 1 - A / Real.log |t| ≤ σ₁) (_ : σ₂ ≤ 2) (_ : σ₁ < σ₂),
    ‖ζ (σ₂ + t * I) - ζ (σ₁ + t * I)‖ ≤  C * Real.log |t| ^ 2 * (σ₂ - σ₁) := by
  admit

lemma ZetaInvBnd_aux' {t : ℝ} (logt_gt_one : 1 < Real.log |t|) : Real.log |t| < Real.log |t| ^ 9 := by
  admit

lemma ZetaInvBnd_aux {t : ℝ} (logt_gt_one : 1 < Real.log |t|) : Real.log |t| ≤ Real.log |t| ^ 9 := by
  admit

lemma ZetaInvBnd_aux2 {A C₁ C₂ : ℝ} (Apos : 0 < A) (C₁pos : 0 < C₁) (C₂pos : 0 < C₂)
    (hA : A ≤ 1 / 2 * (C₁ / (C₂ * 2)) ^ (4 : ℝ)) :
    0 < (C₁ * A ^ (3 / 4 : ℝ) - C₂ * 2 * A)⁻¹ := by
  admit

/-- **ZetaInvBnd**

For any $A>0$ sufficiently small, there is a constant $C>0$ so that
  whenever $1- A / \log^9 |t| \le \sigma < 1+A/\log^9 |t|$ and $3 < |t|$, we have that:
  $$
  1/|\zeta(\sigma+it)| \le C \log^7 |t|.
  $$

PROVIDED SOLUTION:
Let $\sigma$ be given in the prescribed range, and set $\sigma' := 1+ A / \log^9 |t|$.
  Then
  $$
  |\zeta(\sigma+it)| \ge
  |\zeta(\sigma'+it)| - |\zeta(\sigma+it) - \zeta(\sigma'+it)|
  \ge
  C (\sigma'-1)^{3/4}\log |t|^{-1/4} - C \log^2 |t| (\sigma'-\sigma)
  $$
  $$
  \ge
  C A^{3/4} \log |t|^{-7} - C \log^2 |t| (2 A / \log^9 |t|),
  $$
  where we used Lemma \ref{ZetaInvBound2}  and Lemma \ref{Zeta_diff_Bnd}.
  Now by making $A$ sufficiently small (in particular, something like $A = 1/16$ should work), we can guarantee that
  $$
  |\zeta(\sigma+it)| \ge \frac C 2 (\log |t|)^{-7},
  $$
  as desired.
-/
lemma ZetaInvBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9) (1 + A / (Real.log |t|) ^ 9)),
    1 / ‖ζ (σ + t * I)‖ ≤ C * (Real.log |t|) ^ (7 : ℝ) := by
  admit

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

/-!
Annoyingly, it is not immediate from this that $\zeta$ doesn't vanish there! That's because
$1/0 = 0$ in Lean. So we give a second proof of the same fact (refactor this later), with a lower
 bound on $\zeta$ instead of upper bound on $1 / \zeta$.
-/
/-- **ZetaLowerBnd**

For any $A>0$ sufficiently small, there is a constant $C>0$ so that
  whenever $1- A / \log^9 |t| \le \sigma < 1$ and $3 < |t|$, we have that:
  $$
  |\zeta(\sigma+it)| \ge C \log^7 |t|.
  $$

PROVIDED SOLUTION:
Follow same argument.
-/
lemma ZetaLowerBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (c : ℝ) (_ : 0 < c),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9) 1),
    c / (Real.log |t|) ^ (7 : ℝ) ≤ ‖ζ (σ + t * I)‖ := by
  admit

-- **End collaboration 6/20/25**

/-!
Now we get a zero free region.
-/
/-- **ZetaZeroFree**

There is an $A>0$ so that for $1-A/\log^9 |t| \le \sigma < 1$ and $3 < |t|$,
  $$
  \zeta(\sigma+it) \ne 0.
  $$

PROVIDED SOLUTION:
Apply Lemma \ref{ZetaLowerBnd}.
-/
lemma ZetaZeroFree :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / (Real.log |t|) ^ 9) 1),
    ζ (σ + t * I) ≠ 0 := by
  admit

/-- **LogDerivZetaBnd**

There is an $A>0$ so that for $1-A/\log^9 |t| \le \sigma < 1+A/\log^9 |t|$ and $3 < |t|$,
  $$
  |\frac {\zeta'}{\zeta} (\sigma+it)| \ll \log^9 |t|.
  $$

PROVIDED SOLUTION:
Combine the bound on $|\zeta'|$ from Lemma \ref{ZetaDerivUpperBnd} with the
  bound on $1/|\zeta|$ from Lemma \ref{ZetaInvBnd}.
-/
lemma LogDerivZetaBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ico (1 - A / Real.log |t| ^ 9) (1 + A / Real.log |t| ^ 9)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
      C * Real.log |t| ^ 9 := by
  admit

/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/
/-- **ZetaNoZerosOn1Line**

The zeta function does not vanish on the 1-line.

PROVIDED SOLUTION:
This fact is already proved in Stoll's work.
-/
lemma ZetaNoZerosOn1Line (t : ℝ) : ζ (1 + t * I) ≠ 0 := by
  admit

-- **Begin collaboration with the Alpha Proof team! 5/29/25**

lemma ZetaCont : ContinuousOn ζ (univ \ {1}) := by
  admit

/-!
Then, since $\zeta$ doesn't vanish on the 1-line, there is a $\sigma<1$ (depending on $T$), so that
the box $[\sigma,1] \times_{ℂ} [-T,T]$ is free of zeros of $\zeta$.
-/
/-- **ZetaNoZerosInBox**

For any $T>0$, there is a constant $\sigma<1$ so that
  $$
  \zeta(\sigma'+it) \ne 0
  $$
  for all $|t| \leq T$ and $\sigma' \ge \sigma$.

PROVIDED SOLUTION:
Assume not. Then there is a sequence $|t_n| \le T$ and $\sigma_n \to 1$ so that
  $\zeta(\sigma_n + it_n) = 0$.
  By compactness, there is a subsequence $t_{n_k} \to t_0$ along which
  $\zeta(\sigma_{n_k} + it_{n_k}) = 0$.
  If $t_0\ne0$, use the continuity of $\zeta$ to get that $\zeta(1 + it_0) = 0$;
  this is a contradiction.
  If $t_0=0$, $\zeta$ blows up near $1$, so can't be zero nearby.
-/
lemma ZetaNoZerosInBox (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), ζ (σ' + t * I) ≠ 0 := by
  admit

-- **End collaboration**

lemma LogDerivZetaHoloOn {S : Set ℂ} (s_ne_one : 1 ∉ S)
    (nonzero : ∀ s ∈ S, ζ s ≠ 0) :
    HolomorphicOn (fun s ↦ ζ' s / ζ s) S := by
  admit

/-!
We now prove that there's an absolute constant $\sigma_0$ so that $\zeta'/\zeta$ is holomorphic on
a rectangle $[\sigma_2,2] \times_{ℂ} [-3,3] \setminus \{1\}$.
-/
/-- **LogDerivZetaHolcSmallT**

There is a $\sigma_2 < 1$ so that the function
  $$
  \frac {\zeta'}{\zeta}(s)
  $$
  is holomorphic on $\{ \sigma_2 \le \Re s \le 2, |\Im s| \le 3 \} \setminus \{1\}$.

PROVIDED SOLUTION:
The derivative of $\zeta$ is holomorphic away from $s=1$; the denominator $\zeta(s)$ is nonzero
  in this range by Lemma \ref{ZetaNoZerosInBox}.
-/
theorem LogDerivZetaHolcSmallT :
    ∃ (σ₂ : ℝ) (_ : σ₂ < 1), HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( [[ σ₂, 2 ]] ×ℂ [[ -3, 3 ]]) \ {1}) := by
  admit

/-- **LogDerivZetaHolcLargeT**

There is an $A>0$ so that for all $T>3$, the function
  $
  \frac {\zeta'}{\zeta}(s)
  $
  is holomorphic on $\{1-A/\log^9 T \le \Re s \le 2, |\Im s|\le T \}\setminus\{1\}$.

PROVIDED SOLUTION:
The derivative of $\zeta$ is holomorphic away from $s=1$; the denominator $\zeta(s)$ is nonzero
  in this range by Lemma \ref{ZetaZeroFree}.
-/
theorem LogDerivZetaHolcLargeT :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)), ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
      (( (Icc ((1 : ℝ) - A / Real.log T ^ 9) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by
  admit

theorem summable_complex_then_summable_real_part (f : ℕ → ℂ)
    (h : Summable f) : Summable (fun n ↦ (f n).re) := by
  admit

open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients
open scoped ComplexOrder in
theorem dlog_riemannZeta_bdd_on_vertical_lines_generalized
    (σ₀ σ₁ t : ℝ) (σ₀_gt_one : 1 < σ₀) (σ₀_lt_σ₁ : σ₀ ≤ σ₁) :
    ‖(- ζ' (σ₁ + t * I) / ζ (σ₁ + t * I))‖ ≤ ‖ζ' σ₀ / ζ σ₀‖ := by
  admit

theorem triv_bound_zeta :  ∃C ≥ 0, ∀(σ₀ t : ℝ), 1 < σ₀ →
    ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ (σ₀ - 1)⁻¹ + C := by
  admit

/-- **LogDerivZetaBndUnif**

There exist $A, C > 0$ such that
  $$|\frac{\zeta'}{\zeta}(\sigma + it)|\leq C \log |t|^9$$
  whenever $|t|>3$ and $\sigma > 1 - A/\log |t|^9$.

PROVIDED SOLUTION:
For $\sigma$ close to $1$ use Lemma \ref{LogDerivZetaBnd}, otherwise estimate trivially.
-/
lemma LogDerivZetaBndUnif :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 9)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
      C * Real.log |t| ^ 9 := by
  admit
