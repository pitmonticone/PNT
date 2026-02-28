import Mathlib
import PrimeNumberTheoremAnd.RectangleAristotle
import PrimeNumberTheoremAnd.Tactic.AdditiveCombinationAristotle

open Complex BigOperators Nat Classical Real Topology Filter Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E}
  {z w p c A : ℂ} {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E := ∫ x in x₁..x₂, f (x + y * I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E := I • ∫ y in y₁..y₂, f (x + y * I)

noncomputable def HIntegral' (f : ℂ → E) (x₁ x₂ y : ℝ) : E := (1 / (2 * π * I)) • HIntegral f x₁ x₂ y

noncomputable def VIntegral' (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=  (1 / (2 * π * I)) • VIntegral f x y₁ y₂

lemma HIntegral_symm : HIntegral f x₁ x₂ y = - HIntegral f x₂ x₁ y := by
  admit

lemma VIntegral_symm : VIntegral f x y₁ y₂ = - VIntegral f x y₂ y₁ := by
  admit

/-- **RectangleIntegral**

A RectangleIntegral of a function $f$ is one over a rectangle determined by $z$ and $w$ in $\C$.
  We will sometimes denote it by $\int_{z}^{w} f$. (There is also a primed version, which is
  $1/(2\pi i)$ times the original.)
-/
noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E := HIntegral f z.re w.re z.im -
    HIntegral f z.re w.re w.im + VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

/-- A `RectangleIntegral'` of a function `f` is one over a rectangle determined by
  `z` and `w` in `ℂ`, divided by `2 * π * I`. -/
noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w

/- An UpperUIntegral is the integral of a function over a |\_| shape. -/
/-- **UpperUIntegral**

An UpperUIntegral of a function $f$ comes from $\sigma+i\infty$ down to $\sigma+iT$, over to
  $\sigma'+iT$, and back up to $\sigma'+i\infty$.
-/
noncomputable def UpperUIntegral (f : ℂ → E) (σ σ' T : ℝ) : E := HIntegral f σ σ' T +
    I • (∫ y : ℝ in Ici T, f (σ' + y * I)) - I • (∫ y : ℝ in Ici T, f (σ + y * I))

/- A LowerUIntegral is the integral of a function over a |-| shape. -/
/-- **LowerUIntegral**

A LowerUIntegral of a function $f$ comes from $\sigma-i\infty$ up to $\sigma-iT$, over to
  $\sigma'-iT$, and back down to $\sigma'-i\infty$.
-/
noncomputable def LowerUIntegral (f : ℂ → E) (σ σ' T : ℝ) : E := HIntegral f σ σ' (-T) -
    I • (∫ y : ℝ in Iic (-T), f (σ' + y * I)) + I • (∫ y : ℝ in Iic (-T), f (σ + y * I))

/-!
It is very convenient to define integrals along vertical lines in the complex plane, as follows.
-/
/-- **VerticalIntegral**

Let $f$ be a function from $\mathbb{C}$ to $\mathbb{C}$, and let $\sigma$ be a real number.
  Then we define
  $$\int_{(\sigma)}f(s)ds = \int_{\sigma-i\infty}^{\sigma+i\infty}f(s)ds.$$
-/
noncomputable def VerticalIntegral (f : ℂ → E) (σ : ℝ) : E := I • ∫ t : ℝ, f (σ + t * I)

/-!
We also have a version with a factor of $1/(2\pi i)$.
-/
noncomputable abbrev VerticalIntegral' (f : ℂ → E) (σ : ℝ) : E :=
    (1 / (2 * π * I)) • VerticalIntegral f σ

lemma verticalIntegral_split_three (a b : ℝ) (hf : Integrable (fun t : ℝ ↦ f (σ + t * I))) :
    VerticalIntegral f σ = I • (∫ t in Iic a, f (σ + t * I)) + VIntegral f σ a b
    + I • ∫ t in Ici b, f (σ + t * I) := by
  admit

-- set_option trace.Meta.Tactic.simp.rewrite true
/-- **DiffVertRect-eq-UpperLowerUs**

The difference of two vertical integrals and a rectangle is the difference of an upper and a
  lower U integrals.

PROVIDED SOLUTION:
Follows directly from the definitions.
-/
lemma DiffVertRect_eq_UpperLowerUs {σ σ' T : ℝ}
    (f_int_σ : Integrable (fun (t : ℝ) ↦ f (σ + t * I)))
    (f_int_σ' : Integrable (fun (t : ℝ) ↦ f (σ' + t * I))) :
    (VerticalIntegral f σ') - (VerticalIntegral f σ) - (RectangleIntegral f (σ - I * T) (σ' + I * T)) =
    (UpperUIntegral f σ σ' T) - (LowerUIntegral f σ σ' T) := by
  admit

/-- A function is `HolomorphicOn` a set if it is complex differentiable on that set. -/
abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop := DifferentiableOn ℂ f s
/-- **existsDifferentiableOn-of-bddAbove**

If $f$ is differentiable on a set $s$ except at $c\in s$, and $f$ is bounded above on
  $s\setminus\{c\}$, then there exists a differentiable function $g$ on $s$ such that $f$ and $g$
  agree on $s\setminus\{c\}$.

PROVIDED SOLUTION:
This is the Riemann Removable Singularity Theorem, slightly rephrased from what's in Mathlib.
  (We don't care what the function $g$ is, just that it's holomorphic.)
-/
theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E] {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c})) (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E), HolomorphicOn g s ∧ (Set.EqOn f g (s \ {c})) := by
  admit

/-- **HolomorphicOn.vanishesOnRectangle**

If $f$ is holomorphic on a rectangle $z$ and $w$, then the integral of $f$ over the rectangle
  with corners $z$ and $w$ is $0$.

PROVIDED SOLUTION:
This is in a Mathlib PR.
-/
theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E] {U : Set ℂ}
    (f_holo : HolomorphicOn f U) (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 := by
  admit

theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  admit

theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  admit

theorem rectangleIntegral_symm (f : ℂ → E) (z w : ℂ) :
    RectangleIntegral f z w = RectangleIntegral f w z := by
  admit

theorem rectangleIntegral_symm_re (f : ℂ → E) (z w : ℂ) :
    RectangleIntegral f (w.re + z.im * I) (z.re + w.im * I) = - RectangleIntegral f z w := by
  admit

def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

theorem RectangleBorderIntegrable.add {f g : ℂ → E} (hf : RectangleBorderIntegrable f z w)
    (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  admit

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w := by
  admit

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderIntegrable (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := by
  admit

omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderNoPIntegrable (hf : ContinuousOn f (Rectangle z w \ {p}))
    (pNotOnBorder : p ∉ RectangleBorder z w) : RectangleBorderIntegrable f z w := by
  admit

theorem HolomorphicOn.rectangleBorderIntegrable' (hf : HolomorphicOn f (Rectangle z w \ {p}))
    (hp : Rectangle z w ∈ nhds p) : RectangleBorderIntegrable f z w := by
  admit

theorem HolomorphicOn.rectangleBorderIntegrable (hf : HolomorphicOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := by
  admit

/--
Given `x₀ a x₁ : ℝ`, and `y₀ y₁ : ℝ` and a function `f : ℂ → ℂ` so that
both `(t : ℝ) ↦ f(t + y₀ * I)` and `(t : ℝ) ↦ f(t + y₁ * I)` are integrable over both
`t ∈ Icc x₀ a` and `t ∈ Icc a x₁`, we have that
`RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I)` is the sum of
`RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I)` and
`RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I)`.
-/
lemma RectangleIntegralHSplit {a x₀ x₁ y₀ y₁ : ℝ}
    (f_int_x₀_a_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume x₀ a)
    (f_int_a_x₁_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume a x₁)
    (f_int_x₀_a_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume x₀ a)
    (f_int_a_x₁_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume a x₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) := by
  admit

lemma RectangleIntegralHSplit' {a x₀ x₁ y₀ y₁ : ℝ} (ha : a ∈ [[x₀, x₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) := by
  admit

lemma RectangleIntegralVSplit {b x₀ x₁ y₀ y₁ : ℝ}
    (f_int_y₀_b_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume y₀ b)
    (f_int_b_y₁_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume b y₁)
    (f_int_y₀_b_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume y₀ b)
    (f_int_b_y₁_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume b y₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) := by
  admit

lemma RectangleIntegralVSplit' {b x₀ x₁ y₀ y₁ : ℝ} (hb : b ∈ [[y₀, y₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) := by
  admit

lemma RectanglePullToNhdOfPole' [CompleteSpace E] {z₀ z₁ z₂ z₃ p : ℂ}
    (h_orientation : z₀.re ≤ z₃.re ∧ z₀.im ≤ z₃.im ∧ z₁.re ≤ z₂.re ∧ z₁.im ≤ z₂.im)
    (hp : Rectangle z₁ z₂ ∈ 𝓝 p) (hz : Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃)
    (fHolo : HolomorphicOn f (Rectangle z₀ z₃ \ {p})) :
    RectangleIntegral f z₀ z₃ = RectangleIntegral f z₁ z₂ := by
  admit

/-!
The next lemma allows to zoom a big rectangle down to a small square, centered at a pole.
-/
/-- **RectanglePullToNhdOfPole**

If $f$ is holomorphic on a rectangle $z$ and $w$ except at a point $p$, then the integral of $f$
  over the rectangle with corners $z$ and $w$ is the same as the integral of $f$ over a small square
  centered at $p$.

PROVIDED SOLUTION:
Chop the big rectangle with two vertical cuts and two horizontal cuts into smaller rectangles,
  the middle one being the desired square. The integral over each of the outer rectangles
  vanishes, since $f$ is holomorphic there. (The constant $c$ being ``small enough'' here just means
  that the inner square is strictly contained in the big rectangle.)
-/
lemma RectanglePullToNhdOfPole [CompleteSpace E] {z w p : ℂ} (zRe_lt_wRe : z.re ≤ w.re)
    (zIm_lt_wIm : z.im ≤ w.im) (hp : Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0,
    RectangleIntegral f z w = RectangleIntegral f (-c - I * c + p) (c + I * c + p) := by
  admit

lemma RectanglePullToNhdOfPole'' [CompleteSpace E] {z w p : ℂ} (zRe_le_wRe : z.re ≤ w.re)
    (zIm_le_wIm : z.im ≤ w.im) (pInRectInterior : Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0,
    RectangleIntegral' f z w = RectangleIntegral' f (-c - I * c + p) (c + I * c + p) := by
  admit

theorem ResidueTheoremAtOrigin_aux1c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (y + I)⁻¹
    IntervalIntegrable f volume a b := by
  admit

theorem ResidueTheoremAtOrigin_aux1c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (y - I)⁻¹
    IntervalIntegrable f volume a b := by
  admit

theorem ResidueTheoremAtOrigin_aux2c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (1 + y * I)⁻¹
    IntervalIntegrable f volume a b := by
  admit

theorem ResidueTheoremAtOrigin_aux2c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (-1 + y * I)⁻¹
    IntervalIntegrable f volume a b := by
  admit

theorem RectangleIntegral.const_smul (f : ℂ → E) (z w c : ℂ) :
    RectangleIntegral (fun s => c • f s) z w = c • RectangleIntegral f z w := by
  admit

theorem RectangleIntegral.const_mul' (f : ℂ → E) (z w c : ℂ) :
    RectangleIntegral' (fun s => c • f s) z w = c • RectangleIntegral' f z w := by
  admit

theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  admit

theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  admit

lemma Complex.inv_re_add_im : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  admit

lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  admit

lemma continuous_self_div_sq_add_sq (hy : y ≠ 0) : Continuous fun x => x / (x ^ 2 + y ^ 2) := by
  admit

lemma integral_self_div_sq_add_sq (hy : y ≠ 0) : ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  admit

lemma integral_const_div_sq_add_sq (hy : y ≠ 0) : ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) =
    Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  admit

lemma integral_const_div_self_add_im (hy : y ≠ 0) : ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  admit

lemma integral_const_div_re_add_self (hx : x ≠ 0) : ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  admit

lemma ResidueTheoremAtOrigin' {z w c : ℂ} (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by
  admit

theorem ResidueTheoremInRectangle (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) : RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  admit

/-- **ResidueTheoremAtOrigin**

The rectangle (square) integral of $f(s) = 1/s$ with corners $-1-i$ and $1+i$ is equal to
  $2\pi i$.

PROVIDED SOLUTION:
This is a special case of the more general result above.
-/
lemma ResidueTheoremAtOrigin : RectangleIntegral' (fun s ↦ 1 / s) (-1 - I) (1 + I) = 1 := by
  admit

-- TODO: generalize to `f g : ℂ → E`
/-- **ResidueTheoremOnRectangleWithSimplePole**

Suppose that $f$ is a holomorphic function on a rectangle, except for a simple pole at $p$.
  By the latter, we mean that there is a function $g$ holomorphic on the rectangle such that,
  $f = g + A/(s-p)$ for some $A\in\C$. Then the integral of $f$ over the rectangle is $A$.

PROVIDED SOLUTION:
Replace $f$ with $g + A/(s-p)$ in the integral.
  The integral of $g$ vanishes by Lemma \ref{HolomorphicOn.vanishesOnRectangle}.
  To evaluate the integral of $1/(s-p)$, pull everything to a square about the origin using
  Lemma \ref{RectanglePullToNhdOfPole}, and rescale by $c$; what remains is handled by
  Lemma \ref{ResidueTheoremAtOrigin}.
-/
lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p)
    (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) (g) (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  admit

-- theorem nhds_basis_square (p : ℂ) : HasBasis (𝓝 p) (0 < ·) (Square p ·) := by
--   apply Filter.HasBasis.to_hasBasis' Metric.nhds_basis_closedBall <;> intro c hc
--   · refine ⟨c / Real.sqrt 2, div_pos hc (Real.sqrt_pos.mpr zero_lt_two), ?_⟩
--     convert square_subset_closedBall p (c / Real.sqrt 2)
--     field_simp [abs_div, abs_eq_self.mpr hc.le, abs_eq_self.mpr (sqrt_nonneg 2)]
--   · refine square_mem_nhds _ hc.ne.symm

lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
  (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
  ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  admit

theorem BddAbove_on_rectangle_of_bdd_near {z w p : ℂ} {f : ℂ → ℂ}
    (f_cont : ContinuousOn f ((Rectangle z w) \ {p}))
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    BddAbove (norm ∘ f '' ((Rectangle z w) \ {p})) := by
  admit

theorem ResidueTheoremOnRectangleWithSimplePole' {f : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f ((Rectangle z w) \ {p}))
    (near_p : (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = A := by
  admit
