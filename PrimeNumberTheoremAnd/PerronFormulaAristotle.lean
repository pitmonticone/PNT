import Mathlib
import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.UniformlyAristotle
import PrimeNumberTheoremAnd.ResidueCalcOnRectanglesAristotle
import PrimeNumberTheoremAnd.WienerAristotle

set_option lang.lemmaCmd true

open Asymptotics Complex ComplexConjugate Topology Filter Real MeasureTheory Set

open scoped Interval

/-!
In this section, we prove the Perron formula, which plays a key role in our proof of Mellin
inversion.
-/

/-!
The following is preparatory material used in the proof of the Perron formula, see Lemma
\ref{formulaLtOne}.
-/

/- TODO: move to general section. -/
/-- **zeroTendstoDiff**

If the limit of $0$ is $L_1 - L_2$, then $L_1 = L_2$.

PROVIDED SOLUTION:
Obvious.
-/
lemma zeroTendstoDiff (L₁ L₂ : ℂ) (f : ℝ → ℂ) (h : ∀ᶠ T in atTop, f T = 0)
    (h' : Tendsto f atTop (𝓝 (L₂ - L₁))) : L₁ = L₂ := by
  admit

/- TODO: Move this to general section. -/
/-- **RectangleIntegral-tendsTo-VerticalIntegral**

Let $\sigma,\sigma' \in \mathbb{R}$, and $f : \mathbb{C} \to \mathbb{C}$ such that
  the vertical integrals $\int_{(\sigma)}f(s)ds$ and $\int_{(\sigma')}f(s)ds$ exist and
  the horizontal integral $\int_{(\sigma)}^{\sigma'}f(x + yi)dx$ vanishes as $y \to \pm \infty$.
  Then the limit of rectangle integrals
  $$\lim_{T\to\infty}\int_{\sigma-iT}^{\sigma'+iT}f(s)ds =
  \int_{(\sigma')}f(s)ds - \int_{(\sigma)}f(s)ds.$$

PROVIDED SOLUTION:
Almost by definition.
-/
lemma RectangleIntegral_tendsTo_VerticalIntegral {σ σ' : ℝ} {f : ℂ → ℂ}
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (T : ℝ) ↦ RectangleIntegral f (σ - I * T) (σ' + I * T)) atTop
      (𝓝 (VerticalIntegral f σ' - VerticalIntegral f σ)) := by
  admit

lemma verticalIntegral_eq_verticalIntegral {σ σ' : ℝ} {f : ℂ → ℂ}
    (hf : HolomorphicOn f ([[σ, σ']] ×ℂ univ))
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    VerticalIntegral f σ = VerticalIntegral f σ' := by
  admit

lemma verticalIntegral_sub_verticalIntegral_eq_squareIntegral {σ σ' : ℝ} {f : ℂ → ℂ} {p : ℂ}
    (hσ : σ < p.re ∧ p.re < σ') (hf : HolomorphicOn f (Icc σ σ' ×ℂ univ \ {p}))
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0, VerticalIntegral f σ' - VerticalIntegral f σ =
    RectangleIntegral f (-c - c * I + p) (c + c * I + p) := by
  admit

/-- **RectangleIntegral-tendsTo-UpperU**

Let $\sigma,\sigma' \in \mathbb{R}$, and $f : \mathbb{C} \to \mathbb{C}$ such that
  the vertical integrals $\int_{(\sigma)}f(s)ds$ and $\int_{(\sigma')}f(s)ds$ exist and
  the horizontal integral $\int_{(\sigma)}^{\sigma'}f(x + yi)dx$ vanishes as $y \to \pm \infty$.
  Then the limit of rectangle integrals
  $$\int_{\sigma+iT}^{\sigma'+iU}f(s)ds$$
  as $U\to\infty$ is the ``UpperUIntegral'' of $f$.

PROVIDED SOLUTION:
Almost by definition.
-/
lemma RectangleIntegral_tendsTo_UpperU {σ σ' T : ℝ} {f : ℂ → ℂ}
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (U : ℝ) ↦ RectangleIntegral f (σ + I * T) (σ' + I * U)) atTop
      (𝓝 (UpperUIntegral f σ σ' T)) := by
  admit

/-- **RectangleIntegral-tendsTo-LowerU**

Let $\sigma,\sigma' \in \mathbb{R}$, and $f : \mathbb{C} \to \mathbb{C}$ such that
  the vertical integrals $\int_{(\sigma)}f(s)ds$ and $\int_{(\sigma')}f(s)ds$ exist and
  the horizontal integral $\int_{(\sigma)}^{\sigma'}f(x + yi)dx$ vanishes as $y \to -\infty$.
  Then the limit of rectangle integrals
  $$\int_{\sigma-iU}^{\sigma'-iT}f(s)ds$$
  as $U\to\infty$ is the ``LowerUIntegral'' of $f$.

PROVIDED SOLUTION:
Almost by definition.
-/
lemma RectangleIntegral_tendsTo_LowerU {σ σ' T : ℝ} {f : ℂ → ℂ}
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (U : ℝ) ↦ RectangleIntegral f (σ - I * U) (σ' - I * T)) atTop
      (𝓝 (- LowerUIntegral f σ σ' T)) := by
  admit

--%\end{proof}

/-!
TODO : Move to general section
-/
/-- **limitOfConstant**

Let $a:\R\to\C$ be a function, and let $\sigma>0$ be a real number. Suppose that, for all
  $\sigma, \sigma'>0$, we have $a(\sigma')=a(\sigma)$, and that
  $\lim_{\sigma\to\infty}a(\sigma)=0$. Then $a(\sigma)=0$.
-/
lemma limitOfConstant {a : ℝ → ℂ} {σ : ℝ} (σpos : 0 < σ)
    (ha : ∀ (σ' : ℝ) (σ'' : ℝ) (_ : 0 < σ') (_ : 0 < σ''), a σ' = a σ'')
    (ha' : Tendsto a atTop (𝓝 0)) : a σ = 0 := by
  admit

/-- **limitOfConstantLeft**

Let $a:\R\to\C$ be a function, and let $\sigma<-3/2$ be a real number. Suppose that, for all
  $\sigma, \sigma'>0$, we have $a(\sigma')=a(\sigma)$, and that
  $\lim_{\sigma\to-\infty}a(\sigma)=0$. Then $a(\sigma)=0$.
-/
lemma limitOfConstantLeft {a : ℝ → ℂ} {σ : ℝ} (σlt : σ ≤ -3 / 2)
    (ha : ∀ (σ' : ℝ) (σ'' : ℝ) (_ : σ' ≤ -3 / 2) (_ : σ'' ≤ -3 / 2), a σ' = a σ'')
    (ha' : Tendsto a atBot (𝓝 0)) : a σ = 0 := by
  admit

/-- **tendsto-rpow-atTop-nhds-zero-of-norm-lt-one**

Let $x>0$ and $x<1$. Then
  $$\lim_{\sigma\to\infty}x^\sigma=0.$$

PROVIDED SOLUTION:
Standard.
-/
lemma tendsto_rpow_atTop_nhds_zero_of_norm_lt_one {x : ℝ} (xpos : 0 < x) (x_lt_one : x < 1)
    (C : ℝ) :
    Tendsto (fun (σ : ℝ) ↦ x ^ σ * C) atTop (𝓝 0) := by
  admit

/-- **tendsto-rpow-atTop-nhds-zero-of-norm-gt-one**

Let $x>1$. Then $$\lim_{\sigma\to-\infty}x^\sigma=0.$$

PROVIDED SOLUTION:
Standard.
-/
lemma tendsto_rpow_atTop_nhds_zero_of_norm_gt_one {x : ℝ} (x_gt_one : 1 < x) (C : ℝ) :
    Tendsto (fun (σ : ℝ) ↦ x ^ σ * C) atBot (𝓝 0) := by
  admit

-- -- TODO: move near `Complex.cpow_neg`?
-- lemma Complex.cpow_inv_ofReal_pos {a : ℝ} (ha : 0 ≤ a) (r : ℂ) :
--     ((a : ℂ) ^ r)⁻¹ = (a : ℂ)⁻¹ ^ r := by
--   sorry

lemma Complex.cpow_eq_exp_log_ofReal (x : ℝ) (hx : 0 < x) (y : ℂ) :
    (x : ℂ) ^ y = Complex.exp (Real.log x * y) := by
  admit

-- TODO: move near `Complex.mul_cpow_ofReal_nonneg`
lemma Complex.cpow_neg_eq_inv_pow_ofReal_pos {a : ℝ} (ha : 0 < a) (r : ℂ) :
    (a : ℂ) ^ (-r) = (a⁻¹ : ℂ) ^ r := by
  admit

namespace Perron

variable {x σ σ' σ'' T : ℝ}

noncomputable abbrev f (x : ℝ) := fun (s : ℂ) ↦ x ^ s / (s * (s + 1))


lemma f_mul_eq_f {x t : ℝ} (tpos : 0 < t) (xpos : 0 < x) (s : ℂ) :
    f t s * (x : ℂ) ^ (-s) = f (t / x) s := by
  admit

/-- **isHolomorphicOn**

Let $x>0$. Then the function $f(s) = x^s/(s(s+1))$ is holomorphic on the half-plane
  $\{s\in\mathbb{C}:\Re(s)>0\}$.
-/
lemma isHolomorphicOn (xpos : 0 < x) : HolomorphicOn (f x) {0, -1}ᶜ := by
  admit

lemma integral_one_div_const_add_sq_pos (c : ℝ) (hc : 0 < c) : 0 < ∫ (t : ℝ), 1 / (c + t ^ 2) := by
  admit

lemma Integrable.one_div_const_add_sq (c : ℝ) (hc : 0 < c) :
    Integrable fun (t : ℝ) ↦ 1 / (c + t ^ 2) := by
  admit

lemma integralPosAux'_of_le (c₁ c₂ : ℝ) (c₁_pos : 0 < c₁) (hle : c₁ ≤ c₂) :
    0 < ∫ (t : ℝ), 1 / ((c₁ + t ^ 2).sqrt * (c₂ + t ^ 2).sqrt) := by
  admit

lemma integralPosAux' (c₁ c₂ : ℝ) (c₁_pos : 0 < c₁) (c₂_pos : 0 < c₂) :
    0 < ∫ (t : ℝ), 1 / ((c₁ + t^2).sqrt * (c₂ + t^2).sqrt) := by
  admit

/-- **integralPosAux**

The integral
  $$\int_\R\frac{1}{|(1+t^2)(2+t^2)|^{1/2}}dt$$
  is positive (and hence convergent - since a divergent integral is zero in Lean, by
  definition).
-/
lemma integralPosAux : 0 < ∫ (t : ℝ), 1 / ((1 + t^2).sqrt * (2 + t^2).sqrt) := by
  admit

/-- **vertIntBound**

Let $x>0$ and $\sigma>1$. Then
  $$\left|
  \int_{(\sigma)}\frac{x^s}{s(s+1)}ds\right| \leq
    x^\sigma \int_\R\frac{1}{|(1+t ^ 2)(2+t ^ 2)|^{1/2}}dt.$$

PROVIDED SOLUTION:
Triangle inequality and pointwise estimate.
-/
lemma vertIntBound (xpos : 0 < x) (σ_gt_one : 1 < σ) :
    ‖VerticalIntegral (f x) σ‖ ≤
      x ^ σ * ∫ (t : ℝ), 1 / ((1 + t ^ 2).sqrt * (2 + t ^ 2).sqrt) := by
  admit

/-- **vertIntBoundLeft**

Let $x>1$ and $\sigma<-3/2$. Then
  $$\left|
  \int_{(\sigma)}\frac{x^s}{s(s+1)}ds\right| \leq
    x^\sigma \int_\R\frac{1}{|(1/4+t ^ 2)(2+t ^ 2)|^{1/2}}dt.$$

PROVIDED SOLUTION:
Triangle inequality and pointwise estimate.
-/
lemma vertIntBoundLeft (xpos : 0 < x) :
    ∃ C, ∀ (σ : ℝ) (_ : σ < -3 / 2), ‖VerticalIntegral' (f x) σ‖ ≤ C * x ^ σ := by
  admit

lemma map_conj (hx : 0 ≤ x) (s : ℂ) : f x (conj s) = conj (f x s) := by
  admit

theorem isTheta_uniformlyOn_uIcc {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) :
    (fun (σ, (y : ℝ)) ↦ f x (σ + y * I)) =Θ[𝓟 [[σ', σ'']] ×ˢ (atBot ⊔ atTop)]
    ((fun y ↦ 1 / y^2) ∘ Prod.snd) := by
  admit

theorem isTheta_uniformlyOn_uIoc {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) :
    (fun (σ, (y : ℝ)) ↦ f x (σ + y * I)) =Θ[𝓟 (uIoc σ' σ'') ×ˢ (atBot ⊔ atTop)]
    fun (_, y) ↦ 1 / y^2 := by
  admit

lemma isTheta (xpos : 0 < x) :
    ((fun (y : ℝ) ↦ f x (σ + y * I)) =Θ[atBot] fun (y : ℝ) ↦ 1 / y^2) ∧
    (fun (y : ℝ) ↦ f x (σ + y * I)) =Θ[atTop] fun (y : ℝ) ↦ 1 / y^2 := by
  admit

/-- **isIntegrable**

Let $x>0$ and $\sigma\in\R$. Then
  $$\int_{\R}\frac{x^{\sigma+it}}{(\sigma+it)(1+\sigma + it)}dt$$
  is integrable.
-/
lemma isIntegrable (xpos : 0 < x) (σ_ne_zero : σ ≠ 0) (σ_ne_neg_one : σ ≠ -1) :
    Integrable fun (t : ℝ) ↦ f x (σ + t * I) := by
  admit

theorem horizontal_integral_isBigO {x : ℝ} (xpos : 0 < x) (σ' σ'' : ℝ) (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ] :
    (fun (y : ℝ) ↦ ∫ (σ : ℝ) in σ'..σ'', f x (σ + y * I) ∂μ) =O[atBot ⊔ atTop]
      fun y ↦ 1 / y^2 := by
  admit

/-- **tendsto-zero-Lower**

Let $x>0$ and $\sigma',\sigma''\in\R$. Then
  $$\int_{\sigma'}^{\sigma''}\frac{x^{\sigma+it}}{(\sigma+it)(1+\sigma + it)}d\sigma$$
  goes to $0$ as $t\to-\infty$.

PROVIDED SOLUTION:
The numerator is bounded and the denominator tends to infinity.
-/
lemma tendsto_zero_Lower (xpos : 0 < x) (σ' σ'' : ℝ) :
    Tendsto (fun (t : ℝ) ↦ ∫ (σ : ℝ) in σ'..σ'', f x (σ + t * I)) atBot (𝓝 0) := by
  admit

/-- **tendsto-zero-Upper**

Let $x>0$ and $\sigma',\sigma''\in\R$. Then
  $$\int_{\sigma'}^{\sigma''}\frac{x^{\sigma+it}}{(\sigma+it)(1+\sigma + it)}d\sigma$$
  goes to $0$ as $t\to\infty$.

PROVIDED SOLUTION:
The numerator is bounded and the denominator tends to infinity.
-/
lemma tendsto_zero_Upper (xpos : 0 < x) (σ' σ'' : ℝ) :
    Tendsto (fun (t : ℝ) ↦ ∫ (σ : ℝ) in σ'..σ'', f x (σ + t * I)) atTop (𝓝 0) := by
  admit

lemma contourPull {σ' σ'' : ℝ} (xpos : 0 < x) (hσ0 : 0 ∉ [[σ', σ'']]) (hσ1 : -1 ∉ [[σ', σ'']]) :
    VerticalIntegral (f x) σ' = VerticalIntegral (f x) σ'' := by
  admit

/-!
We are ready for the first case of the Perron formula, namely when $x<1$:
-/
/-- **formulaLtOne**

For $x>0$, $\sigma>0$, and $x<1$, we have
  $$
  \frac1{2\pi i}
  \int_{(\sigma)}\frac{x^s}{s(s+1)}ds =0.
  $$
-/
lemma formulaLtOne (xpos : 0 < x) (x_lt_one : x < 1) (σ_pos : 0 < σ)
    : VerticalIntegral (f x) σ = 0 := by
  admit

/-!
The second case is when $x>1$.
Here are some auxiliary lemmata for the second case.
TODO: Move to more general section
-/

theorem HolomorphicOn.upperUIntegral_eq_zero {f : ℂ → ℂ} {σ σ' T : ℝ} (hσ : σ ≤ σ')
    (hf : HolomorphicOn f {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ' ∧ T ≤ z.im})
    (htop : Tendsto (fun y : ℝ ↦ ∫ (x : ℝ) in σ..σ', f (↑x + ↑y * I)) atTop (𝓝 0))
    (hleft : Integrable fun y : ℝ ↦ f (↑σ + ↑y * I))
    (hright : Integrable fun y : ℝ ↦ f (↑σ' + ↑y * I)) :
    UpperUIntegral f σ σ' T = 0 := by
  admit

theorem HolomorphicOn.lowerUIntegral_eq_zero {f : ℂ → ℂ} {σ σ' T : ℝ} (hσ : σ ≤ σ')
    (hf : HolomorphicOn f {z : ℂ | σ ≤ z.re ∧ z.re ≤ σ' ∧ z.im ≤ -T})
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I)) atBot (𝓝 0))
    (hleft : Integrable fun y : ℝ ↦ f (↑σ + ↑y * I))
    (hright : Integrable fun y : ℝ ↦ f (↑σ' + ↑y * I)) :
    LowerUIntegral f σ σ' T = 0 := by
  admit

lemma sPlusOneNeZero {s : ℂ} (s_ne_neg_one : s ≠ -1) : s + 1 ≠ 0 := by
  admit

/-- **keyIdentity**

Let $x\in \R$ and $s \ne 0, -1$. Then
  $$
  \frac{x^\sigma}{s(1+s)} = \frac{x^\sigma}{s} - \frac{x^\sigma}{1+s}
  $$

PROVIDED SOLUTION:
By ring.
-/
lemma keyIdentity (x : ℝ) {s : ℂ} (s_ne_zero : s ≠ 0) (s_ne_neg_one : s ≠ -1) :
    (x : ℂ) ^ s / (s * (s + 1))
      = (x : ℂ) ^ s / s - (x : ℂ) ^ s / (s + 1) := by
  admit

variable {α β : Type*} [LinearOrder β] [NoMaxOrder β] [TopologicalSpace β] [ClosedIciTopology β]
  {y : β} {l : Filter α}

lemma _root_.Filter.Tendsto.eventually_bddAbove {f : α → β} (hf : Tendsto f l (𝓝 y)) :
    ∀ᶠ s in l.smallSets, BddAbove (f '' s) := by
  admit

lemma bddAbove_square_of_tendsto {f : ℂ → β} {x : ℂ} (hf : Tendsto f (𝓝[≠] x) (𝓝 y)) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0, BddAbove (f '' (Square x c \ {x})) := by
  admit

/-- **diffBddAtZero**

Let $x>0$. Then for $0 < c < 1 /2$, we have that the function
  $$
  s ↦ \frac{x^s}{s(s+1)} - \frac1s
  $$
  is bounded above on the rectangle with corners at $-c-i*c$ and $c+i*c$ (except at $s=0$).

PROVIDED SOLUTION:
Applying Lemma \ref{keyIdentity}, the
   function $s ↦ x^s/s(s+1) - 1/s = x^s/s - x^0/s - x^s/(1+s)$. The last term is bounded for $s$
   away from $-1$. The first two terms are the difference quotient of the function $s ↦ x^s$ at
   $0$; since it's differentiable, the difference remains bounded as $s\to 0$.
-/
lemma diffBddAtZero {x : ℝ} (xpos : 0 < x) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0, BddAbove ((norm ∘ (fun (s : ℂ) ↦ (x : ℂ) ^ s / (s * (s + 1)) - 1 / s)) ''
    (Square 0 c \ {0})) := by
  admit

/-- **diffBddAtNegOne**

Let $x>0$. Then for $0 < c < 1 /2$, we have that the function
  $$
  s ↦ \frac{x^s}{s(s+1)} - \frac{-x^{-1}}{s+1}
  $$
  is bounded above on the rectangle with corners at $-1-c-i*c$ and $-1+c+i*c$ (except at $s=-1$).

PROVIDED SOLUTION:
Applying Lemma \ref{keyIdentity}, the
   function $s ↦ x^s/s(s+1) - x^{-1}/(s+1) = x^s/s - x^s/(s+1) - (-x^{-1})/(s+1)$. The first term
   is bounded for $s$
   away from $0$. The last two terms are the difference quotient of the function $s ↦ x^s$ at
   $-1$; since it's differentiable, the difference remains bounded as $s\to -1$.
-/
lemma diffBddAtNegOne {x : ℝ} (xpos : 0 < x) :
    ∀ᶠ (c : ℝ) in 𝓝[>] 0,
    BddAbove ((norm ∘ (fun (s : ℂ) ↦ (x : ℂ) ^ s / (s * (s + 1)) - (-x⁻¹) / (s+1))) ''
      (Square (-1) c \ {-1})) := by
  admit

/-- **residueAtZero**

Let $x>0$. Then for all sufficiently small $c>0$, we have that
  $$
  \frac1{2\pi i}
  \int_{-c-i*c}^{c+ i*c}\frac{x^s}{s(s+1)}ds = 1.
  $$
-/
lemma residueAtZero (xpos : 0 < x) : ∀ᶠ (c : ℝ) in 𝓝[>] 0,
    RectangleIntegral' (f x) (-c - c * I) (c + c * I) = 1 := by
  admit

/-- **residueAtNegOne**

Let $x>0$. Then for all sufficiently small $c>0$, we have that
  $$
  \frac1{2\pi i}
  \int_{-c-i*c-1}^{c+ i*c-1}\frac{x^s}{s(s+1)}ds = -\frac1x.
  $$

PROVIDED SOLUTION:
Compute the integral.
-/
lemma residueAtNegOne (xpos : 0 < x) : ∀ᶠ (c : ℝ) in 𝓝[>] 0,
    RectangleIntegral' (f x) (-c - c * I - 1) (c + c * I - 1) = -x⁻¹ := by
  admit

/-- **residuePull1**

For $x>1$ (of course $x>0$ would suffice) and $\sigma>0$, we have
  $$
  \frac1{2\pi i}
  \int_{(\sigma)}\frac{x^s}{s(s+1)}ds =1
  +
  \frac 1{2\pi i}
  \int_{(-1/2)}\frac{x^s}{s(s+1)}ds.
  $$

PROVIDED SOLUTION:
We pull to a square with corners at $-c-i*c$ and $c+i*c$ for $c>0$
  sufficiently small.
  By Lemma \ref{residueAtZero}, the integral over this square is equal to $1$.
-/
lemma residuePull1 (x_gt_one : 1 < x) (σ_pos : 0 < σ) :
    VerticalIntegral' (f x) σ = 1 + VerticalIntegral' (f x) (-1 / 2) := by
  admit

/-- **residuePull2**

For $x>1$, we have
  $$
  \frac1{2\pi i}
  \int_{(-1/2)}\frac{x^s}{s(s+1)}ds = -1/x +
  \frac 1{2\pi i}
  \int_{(-3/2)}\frac{x^s}{s(s+1)}ds.
  $$

PROVIDED SOLUTION:
Pull contour from $(-1/2)$ to $(-3/2)$.
-/
lemma residuePull2 (x_gt_one : 1 < x) :
    VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) (-1 / 2)
    = -1 / x + VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) (-3 / 2) := by
  admit

/-- **contourPull3**

For $x>1$ and $\sigma<-3/2$, we have
  $$
  \frac1{2\pi i}
  \int_{(-3/2)}\frac{x^s}{s(s+1)}ds = \frac 1{2\pi i}
  \int_{(\sigma)}\frac{x^s}{s(s+1)}ds.
  $$

PROVIDED SOLUTION:
Pull contour from $(-3/2)$ to $(\sigma)$.
-/
lemma contourPull3 (x_gt_one : 1 < x) (σ'le : σ' ≤ -3 / 2) (σ''le : σ'' ≤ -3 / 2) :
    VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) σ' =
      VerticalIntegral' (fun s ↦ x ^ s / (s * (s + 1))) σ'' := by
  admit

/-- **formulaGtOne**

For $x>1$ and $\sigma>0$, we have
  $$
  \frac1{2\pi i}
  \int_{(\sigma)}\frac{x^s}{s(s+1)}ds =1-1/x.
  $$
-/
lemma formulaGtOne (x_gt_one : 1 < x) (σ_pos : 0 < σ) :
    VerticalIntegral' (fun s ↦ x^s / (s * (s + 1))) σ = 1 - 1 / x := by
  admit

/-!
The two together give the Perron formula. (Which doesn't need to be a separate lemma.)

For $x>0$ and $\sigma>0$, we have
$$
\frac1{2\pi i}
\int_{(\sigma)}\frac{x^s}{s(s+1)}ds = \begin{cases}
1-\frac1x & \text{ if }x>1\\
0 & \text{ if } x<1
\end{cases}.
$$
-/

end Perron
