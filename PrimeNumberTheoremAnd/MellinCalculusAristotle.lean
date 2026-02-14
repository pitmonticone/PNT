import Mathlib
import PrimeNumberTheoremAnd.AuxiliaryAristotle

open scoped ContDiff

set_option lang.lemmaCmd true

-- TODO: move near `MeasureTheory.setIntegral_prod`
theorem MeasureTheory.setIntegral_integral_swap {α : Type*} {β : Type*} {E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : MeasureTheory.Measure α}
    {ν : MeasureTheory.Measure β} [NormedAddCommGroup E]
    [MeasureTheory.SigmaFinite ν] [NormedSpace ℝ E] [MeasureTheory.SigmaFinite μ]
    (f : α → β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn (f.uncurry) (s ×ˢ t) (μ.prod ν)) :
    (∫ (x : α) in s, ∫ (y : β) in t, f x y ∂ν ∂μ)
      = ∫ (y : β) in t, ∫ (x : α) in s, f x y ∂μ ∂ν := by
  admit

-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

lemma MeasureTheory.integral_comp_mul_right_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (y * a) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  admit

lemma MeasureTheory.integral_comp_mul_right_I0i_haar_real
    (f : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (y * a) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  admit

lemma MeasureTheory.integral_comp_mul_left_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a * y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  admit

-- TODO: generalize to `RCLike`
lemma MeasureTheory.integral_comp_rpow_I0i_haar_real (f : ℝ → ℝ) {p : ℝ} (hp : p ≠ 0) :
    ∫ (y : ℝ) in Ioi 0, |p| * f (y ^ p) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  admit

lemma MeasureTheory.integral_comp_inv_I0i_haar (f : ℝ → 𝕂) :
    ∫ (y : ℝ) in Ioi 0, f (1 / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  admit

lemma MeasureTheory.integral_comp_div_I0i_haar
    (f : ℝ → 𝕂) {a : ℝ} (ha : 0 < a) :
    ∫ (y : ℝ) in Ioi 0, f (a / y) / y = ∫ (y : ℝ) in Ioi 0, f y / y := by
  admit

theorem Complex.ofReal_rpow {x : ℝ} (h : x > 0) (y : ℝ) :
    (((x : ℝ) ^ (y : ℝ)) : ℝ) = (x : ℂ) ^ (y : ℂ) := by
  admit

@[simp]
lemma Function.support_abs {α : Type*} (f : α → 𝕂) :
    (fun x ↦ ‖f x‖).support = f.support := by
  admit

@[simp]
lemma Function.support_ofReal {f : ℝ → ℝ} :
    (fun x ↦ ((f x) : ℂ)).support = f.support := by
  admit

lemma Function.support_mul_subset_of_subset {s : Set ℝ} {f g : ℝ → 𝕂}
    (fSupp : f.support ⊆ s) : (f * g).support ⊆ s := by
  admit

lemma Function.support_of_along_fiber_subset_subset {α β M : Type*} [Zero M]
    {f : α × β → M} {s : Set α} {t : Set β}
    (hx : ∀ (y : β), (fun x ↦ f (x, y)).support ⊆ s)
    (hy : ∀ (x : α), (fun y ↦ f (x, y)).support ⊆ t) :
    f.support ⊆ s ×ˢ t := by
  admit

lemma Function.support_deriv_subset_Icc {a b : ℝ} {f : ℝ → 𝕂}
    (fSupp : f.support ⊆ Set.Icc a b) :
    (deriv f).support ⊆ Set.Icc a b := by
  admit

lemma IntervalIntegral.integral_eq_integral_of_support_subset_Icc {a b : ℝ} {μ : Measure ℝ}
    [NoAtoms μ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} (h : f.support ⊆ Icc a b) :
    ∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ := by
  admit

lemma SetIntegral.integral_eq_integral_inter_of_support_subset {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s t : Set ℝ} {f : ℝ → E} (h : f.support ⊆ t) (ht : MeasurableSet t) :
    ∫ x in s, f x ∂μ = ∫ x in s ∩ t, f x ∂μ := by
  admit

lemma SetIntegral.integral_eq_integral_inter_of_support_subset_Icc {a b} {μ : Measure ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set ℝ} {f : ℝ → E} (h : f.support ⊆ Icc a b) (hs : Icc a b ⊆ s) :
    ∫ x in s, f x ∂μ = ∫ x in Icc a b, f x ∂μ := by
  admit

lemma intervalIntegral.norm_integral_le_of_norm_le_const' {a b C : ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hab : a ≤ b) (h : ∀ x ∈ (Icc a b), ‖f x‖ ≤ C) :
    ‖∫ x in a..b, f x‖ ≤ C * |b - a| := by
  admit

lemma Filter.TendstoAtZero_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂) (ha : 0 < a)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f (𝓝[>]0) (𝓝 0) := by
  admit

lemma Filter.TendstoAtTop_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂)
    (fSupp : f.support ⊆ Set.Icc a b) :
    Tendsto f atTop (𝓝 0) := by
  admit

lemma Filter.BigO_zero_atZero_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂) (ha : 0 < a)
    (fSupp : f.support ⊆ Set.Icc a b) :
    f =O[𝓝[>] 0] fun _ ↦ (0 : ℝ) := by
  admit

lemma Filter.BigO_zero_atTop_of_support_in_Icc {a b : ℝ} (f : ℝ → 𝕂)
    (fSupp : f.support ⊆ Set.Icc a b) :
    f =O[atTop] fun _ ↦ (0 : ℝ) := by
  admit

lemma deriv.ofReal_comp' {f : ℝ → ℝ} :
    deriv (fun x : ℝ ↦ (f x : ℂ)) = (fun x ↦ ((deriv f) x : ℂ)) := by
  admit

lemma deriv.comp_ofReal' {e : ℂ → ℂ} (hf : Differentiable ℂ e) :
    deriv (fun x : ℝ ↦ e x) = fun (x : ℝ) ↦ deriv e x := by
  admit

/-- **PartialIntegration**

Let $f, g$ be once differentiable functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$ so that $fg'$
  and $f'g$ are both integrable, and $f\cdot g (x)\to 0$ as $x\to 0^+,\infty$.
  Then
  $$
  \int_0^\infty f(x)g'(x) dx = -\int_0^\infty f'(x)g(x)dx.
  $$

PROVIDED SOLUTION:
Partial integration.
-/
lemma PartialIntegration (f g : ℝ → ℂ)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fDerivgInt : IntegrableOn (f * deriv g) (Ioi 0))
    (gDerivfInt : IntegrableOn (deriv f * g) (Ioi 0))
    (lim_at_zero : Tendsto (f * g) (𝓝[>] 0) (𝓝 0))
    (lim_at_inf : Tendsto (f * g) atTop (𝓝 0)) :
    ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
  admit

lemma PartialIntegration_of_support_in_Icc {a b : ℝ} (f g : ℝ → ℂ) (ha : 0 < a)
    (h : a ≤ b)
    (fSupp : f.support ⊆ Set.Icc a b)
    (fDiff : DifferentiableOn ℝ f (Ioi 0))
    (gDiff : DifferentiableOn ℝ g (Ioi 0))
    (fderivCont : ContinuousOn (deriv f) (Ioi 0))
    (gderivCont : ContinuousOn (deriv g) (Ioi 0)) :
    ∫ x in Ioi 0, f x * deriv g x = -∫ x in Ioi 0, deriv f x * g x := by
  admit

/-!
In this section, we define the Mellin transform (already in Mathlib, thanks to David Loeffler),
prove its inversion formula, and
derive a number of important properties of some special functions and bumpfunctions.

Def: (Already in Mathlib)
Let $f$ be a function from $\mathbb{R}_{>0}$ to $\mathbb{C}$. We define the Mellin transform of
$f$ to be the function $\mathcal{M}(f)$ from $\mathbb{C}$ to $\mathbb{C}$ defined by
$$\mathcal{M}(f)(s) = \int_0^\infty f(x)x^{s-1}dx.$$

[Note: My preferred way to think about this is that we are integrating over the multiplicative
group $\mathbb{R}_{>0}$, multiplying by a (not necessarily unitary!) character $|\cdot|^s$, and
integrating with respect to the invariant Haar measure $dx/x$. This is very useful in the kinds
of calculations carried out below. But may be more difficult to formalize as things now stand. So
we might have clunkier calculations, which ``magically'' turn out just right - of course they're
explained by the aforementioned structure...]
-/


local notation (name := mellintransform) "𝓜" => mellin


/-!
Finally, we need Mellin Convolutions and properties thereof.
-/
/-- **MellinConvolution**

Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$. Then we define the
  Mellin convolution of $f$ and $g$ to be the function $f\ast g$ from $\mathbb{R}_{>0}$
  to $\mathbb{C}$ defined by
  $$(f\ast g)(x) = \int_0^\infty f(y)g(x/y)\frac{dy}{y}.$$
-/
noncomputable def MellinConvolution (f g : ℝ → 𝕂) (x : ℝ) : 𝕂 :=
  ∫ y in Ioi 0, f y * g (x / y) / y

/-!
Let us start with a simple property of the Mellin convolution.
-/
/-- **MellinConvolutionSymmetric**

Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{R}$ or $\mathbb{C}$, for $x\neq0$,
  $$
    (f\ast g)(x)=(g\ast f)(x)
    .
  $$

PROVIDED SOLUTION:
By Definition \ref{MellinConvolution},
  $$
    (f\ast g)(x) = \int_0^\infty f(y)g(x/y)\frac{dy}{y}
  $$
  in which we change variables to $z=x/y$:
  $$
    (f\ast g)(x) = \int_0^\infty f(x/z)g(z)\frac{dz}{z}
    =(g\ast f)(x)
    .
  $$
-/
lemma MellinConvolutionSymmetric (f g : ℝ → 𝕂) {x : ℝ} (xpos : 0 < x) :
    MellinConvolution f g x = MellinConvolution g f x := by
  admit

open Pointwise in
lemma support_MellinConvolution_subsets {f g : ℝ → 𝕂} {A B : Set ℝ} (hf : f.support ⊆ A)
    (hg : g.support ⊆ B) : (MellinConvolution f g).support ⊆ A * B := by
  admit

open Pointwise in
lemma support_MellinConvolution (f g : ℝ → 𝕂) :
    (MellinConvolution f g).support ⊆ f.support * g.support := by
  admit

/-!
The Mellin transform of a convolution is the product of the Mellin transforms.
-/
/-- **MellinConvolutionTransform**

Let $f$ and $g$ be functions from $\mathbb{R}_{>0}$ to $\mathbb{C}$ such that
  $$
    (x,y)\mapsto f(y)\frac{g(x/y)}yx^{s-1}
    
  $$
  is absolutely integrable on $[0,\infty)^2$.
  Then
  $$\mathcal{M}(f\ast g)(s) = \mathcal{M}(f)(s)\mathcal{M}(g)(s).$$

PROVIDED SOLUTION:
By Definitions \ref{MellinTransform} and \ref{MellinConvolution}
  $$
    \mathcal M(f\ast g)(s)=
    \int_0^\infty \int_0^\infty f(y)g(x/y)x^{s-1}\frac{dy}ydx
  $$
  By ((equation assm_integrable_Mconv)) and Fubini's theorem,
  $$
    \mathcal M(f\ast g)(s)=
    \int_0^\infty \int_0^\infty f(y)g(x/y)x^{s-1}dx\frac{dy}y
  $$
  in which we change variables from $x$ to $z=x/y$:
  $$
    \mathcal M(f\ast g)(s)=
    \int_0^\infty \int_0^\infty f(y)g(z)y^{s-1}z^{s-1}dzdy
  $$
  which, by Definition \ref{MellinTransform}, is
  $$
    \mathcal M(f\ast g)(s)=
    \mathcal M(f)(s)\mathcal M(g)(s)
    .
  $$
-/
lemma MellinConvolutionTransform (f g : ℝ → ℂ) (s : ℂ)
    (hf : IntegrableOn (fun x y ↦ f y * g (x / y) / (y : ℂ) * (x : ℂ) ^ (s - 1)).uncurry
      (Ioi 0 ×ˢ Ioi 0)) :
    𝓜 (MellinConvolution f g) s = 𝓜 f s * 𝓜 g s := by
  admit

lemma mem_within_strip (σ₁ σ₂ : ℝ) :
    {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂} ∈
      𝓟 {s | σ₁ ≤ s.re ∧ s.re ≤ σ₂} := by
  admit

lemma MellinOfPsi_aux {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    {s : ℂ} (hs : s ≠ 0) :
    ∫ (x : ℝ) in Ioi 0, (ν x) * (x : ℂ) ^ (s - 1) =
    - (1 / s) * ∫ (x : ℝ) in Ioi 0, (deriv ν x) * (x : ℂ) ^ s := by
  admit

/-!
The $\nu$ function has Mellin transform $\mathcal{M}(\nu)(s)$ which is entire and decays (at
least) like $1/|s|$.

[Of course it decays faster than any power of $|s|$, but it turns out that we will just need one
power.]
-/

-- filter-free version:
/-- **MellinOfPsi**

The Mellin transform of $\nu$ is
  $$\mathcal{M}(\nu)(s) =  O\left(\frac{1}{|s|}\right),$$
  as $|s|\to\infty$ with $\sigma_1 \le \Re(s) \le 2$.

PROVIDED SOLUTION:
Integrate by parts:
  $$
  \left|\int_0^\infty \nu(x)x^s\frac{dx}{x}\right| =
  \left|-\int_0^\infty \nu'(x)\frac{x^{s}}{s}dx\right|
  $$
  $$
  \le \frac{1}{|s|} \int_{1/2}^2|\nu'(x)|x^{\Re(s)}dx.
  $$
  Since $\Re(s)$ is bounded, the right-hand side is bounded by a
  constant times $1/|s|$.
-/
lemma MellinOfPsi {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ C > 0, ∀ (σ₁ : ℝ) (_ : 0 < σ₁) (s : ℂ) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2),
    ‖𝓜 (fun x ↦ (ν x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
  admit

/-!
We can make a delta spike out of this bumpfunction, as follows.
-/
/-- **DeltaSpike**

Let $\nu$ be a bumpfunction supported in $[1/2,2]$. Then for any $\epsilon>0$, we define the
  delta spike $\nu_\epsilon$ to be the function from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
  $$\nu_\epsilon(x) = \frac{1}{\epsilon}\nu\left(x^{\frac{1}{\epsilon}}\right).$$
-/
noncomputable def DeltaSpike (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ν (x ^ (1 / ε)) / ε

/-!
This spike still has mass one:
-/
/-- **DeltaSpikeMass**

For any $\epsilon>0$, we have
  $$\int_0^\infty \nu_\epsilon(x)\frac{dx}{x} = 1.$$

PROVIDED SOLUTION:
Substitute $y=x^{1/\epsilon}$, and use the fact that $\nu$ has mass one, and that $dx/x$ is Haar
  measure.
-/
lemma DeltaSpikeMass {ν : ℝ → ℝ} (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ}
    (εpos : 0 < ε) : ∫ x in Ioi 0, ((DeltaSpike ν ε) x) / x = 1 := by
  admit

lemma DeltaSpikeSupport_aux {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x).support ⊆ Icc (2 ^ (-ε)) (2 ^ ε) := by
  admit

lemma DeltaSpikeSupport' {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    DeltaSpike ν ε x ≠ 0 → x ∈ Icc (2 ^ (-ε)) (2 ^ ε) := by
  admit

lemma DeltaSpikeSupport {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    x ∉ Icc (2 ^ (-ε)) (2 ^ ε) → DeltaSpike ν ε x = 0 := by
  admit

@[fun_prop]
lemma DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by
  admit

lemma DeltaSpikeOfRealContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ (DeltaSpike ν ε x : ℂ)) := by
  admit

/-!
The Mellin transform of the delta spike is easy to compute.
-/
/-- **MellinOfDeltaSpike**

For any $\epsilon>0$, the Mellin transform of $\nu_\epsilon$ is
  $$\mathcal{M}(\nu_\epsilon)(s) = \mathcal{M}(\nu)\left(\epsilon s\right).$$

PROVIDED SOLUTION:
Substitute $y=x^{1/\epsilon}$, use Haar measure; direct calculation.
-/
theorem MellinOfDeltaSpike (ν : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) (s : ℂ) :
    𝓜 (fun x ↦ (DeltaSpike ν ε x : ℂ)) s = 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by
  admit

/-!
In particular, for $s=1$, we have that the Mellin transform of $\nu_\epsilon$ is $1+O(\epsilon)$.
-/
/-- **MellinOfDeltaSpikeAt1**

For any $\epsilon>0$, we have
  $$\mathcal{M}(\nu_\epsilon)(1) =
  \mathcal{M}(\nu)(\epsilon).$$

PROVIDED SOLUTION:
This is immediate from the above theorem.
-/
lemma MellinOfDeltaSpikeAt1 (ν : ℝ → ℝ) {ε : ℝ} (εpos : ε > 0) :
    𝓜 (fun x ↦ (DeltaSpike ν ε x : ℂ)) 1 = 𝓜 (fun x ↦ (ν x : ℂ)) ε := by
  admit

/-- **MellinOfDeltaSpikeAt1-asymp**

As $\epsilon\to 0$, we have
  $$\mathcal{M}(\nu_\epsilon)(1) = 1+O(\epsilon).$$

PROVIDED SOLUTION:
By Lemma \ref{MellinOfDeltaSpikeAt1},
  $$
    \mathcal M(\nu_\epsilon)(1)=\mathcal M(\nu)(\epsilon)
  $$
  which by Definition \ref{MellinTransform} is
  $$
    \mathcal M(\nu)(\epsilon)=\int_0^\infty\nu(x)x^{\epsilon-1}dx
    .
  $$
  Since $\nu(x) x^{\epsilon-1}$ is integrable (because $\nu$ is continuous and compactly
  supported),
  $$
    \mathcal M(\nu)(\epsilon)-\int_0^\infty\nu(x)\frac{dx}x
    =\int_0^\infty\nu(x)(x^{\epsilon-1}-x^{-1})dx
    .
  $$
  By Taylor's theorem,
  $$
    x^{\epsilon-1}-x^{-1}=O(\epsilon)
  $$
  so, since $\nu$ is absolutely integrable,
  $$
    \mathcal M(\nu)(\epsilon)-\int_0^\infty\nu(x)\frac{dx}x=O(\epsilon)
    .
  $$
  We conclude the proof using Theorem \ref{SmoothExistence}.
-/
lemma MellinOfDeltaSpikeAt1_asymp {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) :
    (fun (ε : ℝ) ↦ (𝓜 (fun x ↦ (ν x : ℂ)) ε) - 1) =O[𝓝[>]0] id := by
  admit

/-!
Let $1_{(0,1]}$ be the function from $\mathbb{R}_{>0}$ to $\mathbb{C}$ defined by
$$1_{(0,1]}(x) = \begin{cases}
1 & \text{ if }x\leq 1\\
0 & \text{ if }x>1
\end{cases}.$$
This has Mellin transform:
[Note: this already exists in mathlib]
-/
/-- **MellinOf1**

The Mellin transform of $1_{(0,1]}$ is
  $$\mathcal{M}(1_{(0,1]})(s) = \frac{1}{s}.$$

PROVIDED SOLUTION:
This is a straightforward calculation.
-/
lemma MellinOf1 (s : ℂ) (h : s.re > 0) :
    𝓜 ((fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0)) s = 1 / s := by
  admit

/-!
What will be essential for us is properties of the smooth version of $1_{(0,1]}$, obtained as the
 Mellin convolution of $1_{(0,1]}$ with $\nu_\epsilon$.
-/
/-- **Smooth1**

Let $\epsilon>0$. Then we define the smooth function $\widetilde{1_{\epsilon}}$ from
  $\mathbb{R}_{>0}$ to $\mathbb{C}$ by
  $$\widetilde{1_{\epsilon}} = 1_{(0,1]}\ast\nu_\epsilon.$$

PROVIDED SOLUTION:
Let $c:=2^\epsilon > 1$, in terms of which we wish to prove
  $$
    -1 < c \log c - c .
  $$
  Letting $f(x):=x\log x - x$, we can rewrite this as $f(1) < f(c)$.
  Since
  $$
    \frac {d}{dx}f(x) = \log x > 0 ,
  $$
  $f$ is monotone increasing on [1, \infty), and we are done.
-/
noncomputable def Smooth1 (ν : ℝ → ℝ) (ε : ℝ) : ℝ → ℝ :=
  MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0) (DeltaSpike ν ε)

-- This lemma might not be necessary, but the RHS is supported on [0, infinity), which makes
-- results like `support_MellinConvolution_subsets` easier to apply.
lemma Smooth1_def_ite {ν : ℝ → ℝ} {ε x : ℝ} (xpos : 0 < x) :
    Smooth1 ν ε x = MellinConvolution (fun x ↦ if 0 < x ∧ x ≤ 1 then 1 else 0)
      (fun x ↦ if x < 0 then 0 else DeltaSpike ν ε x) x := by
  admit

/-% ** Wrong delimiters on purpose, no need to include this in blueprint
\begin{lemma}[Smooth1Properties_estimate]\label{Smooth1Properties_estimate}
\lean{Smooth1Properties_estimate}\leanok
For $\epsilon>0$,
$$
  \log2>\frac{1-2^{-\epsilon}}\epsilon
$$
\end{lemma}
%-/

lemma Smooth1Properties_estimate {ε : ℝ} (εpos : 0 < ε) :
    (1 - 2 ^ (-ε)) / ε < Real.log 2 := by
  admit

/-!
In particular, we have the following two properties.
-/

lemma Smooth1Properties_below_aux {x ε : ℝ} (hx : x ≤ 1 - Real.log 2 * ε) (εpos : 0 < ε) :
    x < 2 ^ (-ε) := by
  admit

/-- **Smooth1Properties-below**

Fix $\epsilon>0$. There is an absolute constant $c>0$ so that:
  If $0 < x \leq (1-c\epsilon)$, then
  $$\widetilde{1_{\epsilon}}(x) = 1.$$

PROVIDED SOLUTION:
Opening the definition, we have that the Mellin convolution of $1_{(0,1]}$ with $\nu_\epsilon$ is
  $$
  \int_0^\infty 1_{(0,1]}(y)\nu_\epsilon(x/y)\frac{dy}{y}
  =
  \int_0^1 \nu_\epsilon(x/y)\frac{dy}{y}.
  $$
  The support of $\nu_\epsilon$ is contained in $[1/2^\epsilon,2^\epsilon]$, so it suffices to
  consider $y \in [1/2^\epsilon x,2^\epsilon x]$ for nonzero contributions. If $x < 2^{-\epsilon}$,
  then the integral is the same as that over $(0,\infty)$:
  $$
  \int_0^1 \nu_\epsilon(x/y)\frac{dy}{y}
  =
  \int_0^\infty \nu_\epsilon(x/y)\frac{dy}{y},
  $$
  in which we change variables to $z=x/y$ (using $x>0$):
  $$
  \int_0^\infty \nu_\epsilon(x/y)\frac{dy}{y}
  =
  \int_0^\infty \nu_\epsilon(z)\frac{dz}{z},
  $$
  which is equal to one by Lemma \ref{DeltaSpikeMass}.
  We then choose
  $$
    c:=\log 2,
  $$
  which satisfies
  $$
    c > \frac{1-2^{-\epsilon}}\epsilon
  $$
  by Lemma \ref{Smooth1Properties_estimate}, so
  $$
    1-c\epsilon < 2^{-\epsilon}.
  $$
-/
lemma Smooth1Properties_below {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∃ (c : ℝ), 0 < c ∧ c = Real.log 2 ∧
      ∀ (ε x) (_ : 0 < ε), 0 < x → x ≤ 1 - c * ε → Smooth1 ν ε x = 1 := by
  admit

lemma Smooth1Properties_above_aux {x ε : ℝ} (hx : 1 + (2 * Real.log 2) * ε ≤ x)
    (hε : ε ∈ Ioo 0 1) :
    2 ^ ε < x := by
  admit

lemma Smooth1Properties_above_aux2 {x y ε : ℝ} (hε : ε ∈ Ioo 0 1) (hy : y ∈ Ioc 0 1)
  (hx2 : 2 ^ ε < x) :
    2 < (x / y) ^ (1 / ε) := by
  admit

/-- **Smooth1Properties-above**

Fix $0<\epsilon<1$. There is an absolute constant $c>0$ so that:
  if $x\geq (1+c\epsilon)$, then
  $$\widetilde{1_{\epsilon}}(x) = 0.$$

PROVIDED SOLUTION:
Again the Mellin convolution is
  $$\int_0^1 \nu_\epsilon(x/y)\frac{dy}{y},$$
  but now if $x > 2^\epsilon$, then the support of $\nu_\epsilon$ is disjoint
  from the region of integration, and hence the integral is zero.
  We choose
  $$
    c:=2\log 2
    .
  $$
  By Lemma \ref{Smooth1Properties_estimate},
  $$
    c > 2\frac{1-2^{-\epsilon}}\epsilon > 2^\epsilon\frac{1-2^{-\epsilon}}\epsilon
    =
    \frac{2^\epsilon-1}\epsilon,
  $$
  so
  $$
    1+c\epsilon > 2^\epsilon.
  $$
-/
lemma Smooth1Properties_above {ν : ℝ → ℝ} (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    ∃ (c : ℝ), 0 < c ∧ c = 2 * Real.log 2 ∧
      ∀ (ε x) (_ : ε ∈ Ioo 0 1), 1 + c * ε ≤ x → Smooth1 ν ε x = 0 := by
  admit

lemma DeltaSpikeNonNeg_of_NonNeg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
     {x ε : ℝ} (xpos : 0 < x) (εpos : 0 < ε) :
    0 ≤ DeltaSpike ν ε x := by
  admit

lemma MellinConvNonNeg_of_NonNeg {f g : ℝ → ℝ} (f_nonneg : ∀ x > 0, 0 ≤ f x)
    (g_nonneg : ∀ x > 0, 0 ≤ g x) {x : ℝ} (xpos : 0 < x) :
    0 ≤ MellinConvolution f g x := by
  admit

/-- **Smooth1Nonneg**

If $\nu$ is nonnegative, then $\widetilde{1_{\epsilon}}(x)$ is nonnegative.

PROVIDED SOLUTION:
By Definitions \ref{Smooth1}, \ref{MellinConvolution} and \ref{DeltaSpike}
  $$
    \widetilde{1_\epsilon}(x)
    =\int_0^\infty 1_{(0,1]}(y)\frac1\epsilon\nu((x/y)^{\frac1\epsilon}) \frac{dy}y
  $$
  and all the factors in the integrand are nonnegative.
-/
lemma Smooth1Nonneg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x) {ε x : ℝ}
    (xpos : 0 < x) (εpos : 0 < ε) : 0 ≤ Smooth1 ν ε x := by
  admit

lemma Smooth1LeOne_aux {x ε : ℝ} {ν : ℝ → ℝ} (xpos : 0 < x) (εpos : 0 < ε)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    ∫ (y : ℝ) in Ioi 0, ν ((x / y) ^ (1 / ε)) / ε / y = 1 := by
  admit

/-- **Smooth1LeOne**

If $\nu$ is nonnegative and has mass one, then $\widetilde{1_{\epsilon}}(x)\le 1$, $\forall x>0$.

PROVIDED SOLUTION:
By Definitions \ref{Smooth1}, \ref{MellinConvolution} and \ref{DeltaSpike}
  $$
    \widetilde{1_\epsilon}(x)
    =\int_0^\infty 1_{(0,1]}(y)\frac1\epsilon\nu((x/y)^{\frac1\epsilon}) \frac{dy}y
  $$
  and since $1_{(0,1]}(y)\le 1$, and all the factors in the integrand are nonnegative,
  $$
    \widetilde{1_\epsilon}(x)\le\int_0^\infty \frac1\epsilon\nu((x/y)^{\frac1\epsilon}) \frac{dy}y
  $$
  (because in mathlib the integral of a non-integrable function is $0$, for the inequality above
  to be true, we must prove that $\nu((x/y)^{\frac1\epsilon})/y$ is integrable; this follows from
  the computation below).
  We then change variables to $z=(x/y)^{\frac1\epsilon}$:
  $$
    \widetilde{1_\epsilon}(x)\le\int_0^\infty \nu(z) \frac{dz}z
  $$
  which by Theorem \ref{SmoothExistence} is 1.
-/
lemma Smooth1LeOne {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (εpos : 0 < ε) {x : ℝ} (xpos : 0 < x) :
    Smooth1 ν ε x ≤ 1 := by
  admit

/-!
Combining the above, we have the following three Main Lemmata of this section on the Mellin
transform of $\widetilde{1_{\epsilon}}$.
-/
/-- **MellinOfSmooth1a**

Fix  $\epsilon>0$. Then the Mellin transform of $\widetilde{1_{\epsilon}}$ is
  $$\mathcal{M}(\widetilde{1_{\epsilon}})(s) =
  \frac{1}{s}\left(\mathcal{M}(\nu)\left(\epsilon s\right)\right).$$

PROVIDED SOLUTION:
By Definition \ref{Smooth1},
  $$
    \mathcal M(\widetilde{1_\epsilon})(s)
    =\mathcal M(1_{(0,1]}\ast\nu_\epsilon)(s)
    .
  $$
  We wish to apply Theorem \ref{MellinConvolutionTransform}.
  To do so, we must prove that
  $$
    (x,y)\mapsto 1_{(0,1]}(y)\nu_\epsilon(x/y)/y
  $$
  is integrable on $[0,\infty)^2$.
  It is actually easier to do this for the convolution: $\nu_\epsilon\ast 1_{(0,1]}$, so we use
  Lemma \ref{MellinConvolutionSymmetric}: for $x\neq0$,
  $$
    1_{(0,1]}\ast\nu_\epsilon(x)=\nu_\epsilon\ast 1_{(0,1]}(x)
    .
  $$
  Now, for $x=0$, both sides of the equation are 0, so the equation also holds for $x=0$.
  Therefore,
  $$
    \mathcal M(\widetilde{1_\epsilon})(s)
    =\mathcal M(\nu_\epsilon\ast 1_{(0,1]})(s)
    .
  $$
  Now,
  $$
    (x,y)\mapsto \nu_\epsilon(y)1_{(0,1]}(x/y)\frac{x^{s-1}}y
  $$
  has compact support that is bounded away from $y=0$ (specifically
  $y\in[2^{-\epsilon},2^\epsilon]$ and $x\in(0,y]$), so it is integrable.
  We can thus apply Theorem \ref{MellinConvolutionTransform} and find
  $$
    \mathcal M(\widetilde{1_\epsilon})(s)
    =\mathcal M(\nu_\epsilon)(s)\mathcal M(1_{(0,1]})(s)
    .
  $$
  By Lemmas \ref{MellinOf1} and \ref{MellinOfDeltaSpike},
  $$
    \mathcal M(\widetilde{1_\epsilon})(s)
    =\frac1s\mathcal M(\nu)(\epsilon s)
    .
  $$
-/
lemma MellinOfSmooth1a {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {s : ℂ} (hs : 0 < s.re) :
    𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s =
      s⁻¹ * 𝓜 (fun x ↦ (ν x : ℂ)) (ε * s) := by
  admit

/-- **MellinOfSmooth1b**

Given $0<\sigma_1\le\sigma_2$, for any $s$ such that $\sigma_1\le\mathcal Re(s)\le\sigma_2$,
  we have
  $$\mathcal{M}(\widetilde{1_{\epsilon}})(s) = O\left(\frac{1}{\epsilon|s|^2}\right).$$

PROVIDED SOLUTION:
Use Lemma \ref{MellinOfSmooth1a} and the bound in Lemma \ref{MellinOfPsi}.
-/
lemma MellinOfSmooth1b {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (σ₁ : ℝ) (_ : 0 < σ₁)
    (s) (_ : σ₁ ≤ s.re) (_ : s.re ≤ 2) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1),
    ‖𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ C * (ε * ‖s‖ ^ 2)⁻¹ := by
  admit

/-- **MellinOfSmooth1c**

At $s=1$, we have
  $$\mathcal{M}(\widetilde{1_{\epsilon}})(1) = 1+O(\epsilon)).$$

PROVIDED SOLUTION:
Follows from Lemmas \ref{MellinOfSmooth1a}, \ref{MellinOfDeltaSpikeAt1} and
  \ref{MellinOfDeltaSpikeAt1_asymp}.
-/
lemma MellinOfSmooth1c {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : ν.support ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) :
    (fun ε ↦ 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) 1 - 1) =O[𝓝[>]0] id := by
  admit

/-- **Smooth1ContinuousAt**

Fix a nonnegative, continuously differentiable function $F$ on $\mathbb{R}$ with support in
  $[1/2,2]$. Then for any $\epsilon>0$, the function
  $x \mapsto \int_{(0,\infty)} x^{1+it} \widetilde{1_{\epsilon}}(x) dx$ is continuous at any $y>0$.

PROVIDED SOLUTION:
Use Lemma \ref{MellinconvolutionSymmetric} to write $\widetilde{1_{\epsilon}}(x)$ as an integral
  over an integral near $1$, in particular avoiding the singularity at $0$. The integrand may be
  bounded by $2^{\epsilon}\nu_\epsilon(t)$ which is independent of $x$ and we can use dominated
  convergence to prove continuity.
-/
lemma Smooth1ContinuousAt {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : SmoothingF.support ⊆ Icc (1 / 2) 2)
    {ε : ℝ} (εpos : 0 < ε) {y : ℝ} (ypos : 0 < y) :
    ContinuousAt (fun x ↦ Smooth1 SmoothingF ε x) y := by
  admit

lemma Smooth1MellinConvergent {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) : MellinConvergent (fun x ↦ (Smooth1 Ψ ε x : ℂ)) s := by
  admit

lemma Smooth1MellinDifferentiable {Ψ : ℝ → ℝ} {ε : ℝ} (diffΨ : ContDiff ℝ 1 Ψ)
    (suppΨ : Ψ.support ⊆ Icc (1 / 2) 2) (hε : ε ∈ Ioo 0 1)
    (Ψnonneg : ∀ x > 0, 0 ≤ Ψ x) (mass_one : ∫ x in Ioi 0, Ψ x / x = 1)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (𝓜 (fun x ↦ (Smooth1 Ψ ε x : ℂ))) s := by
  admit