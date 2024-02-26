import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Meromorphic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import EulerProducts.LSeries
import PrimeNumberTheoremAnd.Rectangle

open Complex BigOperators Nat Classical Real Topology Filter Set MeasureTheory intervalIntegral

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E}
  {z w p c A : ℂ} {x x₁ x₂ y y₁ y₂ σ : ℝ}

/-%%
\begin{definition}[RectangleIntegral]\label{RectangleIntegral}\lean{RectangleIntegral}\leanok
A RectangleIntegral of a function $f$ is one over a rectangle determined by $z$ and $w$ in $\C$.
We will sometimes denote it by $\int_{z}^{w} f$. (There is also a primed version, which is $1/(2\pi i)$ times the original.)
\end{definition}
%%-/
/-- A `RectangleIntegral` of a function `f` is one over a rectangle determined by
  `z` and `w` in `ℂ`. -/
noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    ((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
     + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- A `RectangleIntegral'` of a function `f` is one over a rectangle determined by
  `z` and `w` in `ℂ`, divided by `2 * π * I`. -/
noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1/(2 * π * I)) • RectangleIntegral f z w

/-%%
An UpperUIntegral is the integral of a function over a |\_| shape.
\begin{definition}\label{UpperUIntegral}\lean{UpperUIntegral}\leanok
An UpperUIntegral of a function $f$ comes from $\sigma+i\infty$ down to $\sigma+iT$, over to $\sigma'+iT$, and back up to $\sigma'+i\infty$.
\end{definition}
%%-/
noncomputable def UpperUIntegral (f : ℂ → E) (σ σ' T : ℝ) : E :=
    ((∫ x : ℝ in σ..σ', f (x + T * I))
     + I • (∫ y : ℝ in Ici T, f (σ' + y * I)) - I • ∫ y : ℝ in Ici T, f (σ + y * I))

/-%%
A LowerUIntegral is the integral of a function over a |-| shape.
\begin{definition}[LowerUIntegral]\label{LowerUIntegral}\lean{LowerUIntegral}\leanok
A LowerUIntegral of a function $f$ comes from $\sigma-i\infty$ up to $\sigma-iT$, over to $\sigma'-iT$, and back down to $\sigma'-i\infty$.
\end{definition}
%%-/
noncomputable def LowerUIntegral (f : ℂ → E) (σ σ' T : ℝ) : E :=
    ((∫ x : ℝ in σ..σ', f (x - T * I))
     - I • (∫ y : ℝ in Iic (-T), f (σ' + y * I)) + I • ∫ y : ℝ in Iic (-T), f (σ + y * I))


/-%%
It is very convenient to define integrals along vertical lines in the complex plane, as follows.
\begin{definition}[VerticalIntegral]\label{VerticalIntegral}\leanok
Let $f$ be a function from $\mathbb{C}$ to $\mathbb{C}$, and let $\sigma$ be a real number. Then we define
$$\int_{(\sigma)}f(s)ds = \int_{\sigma-i\infty}^{\sigma+i\infty}f(s)ds.$$
\end{definition}
%%-/
noncomputable def VerticalIntegral (f : ℂ → E) (σ : ℝ) : E :=
    I • ∫ t : ℝ, f (σ + t * I)

--%% We also have a version with a factor of $1/(2\pi i)$.
noncomputable abbrev VerticalIntegral' (f : ℂ → E) (σ : ℝ) : E :=
    (1 / (2 * π * I)) • VerticalIntegral f σ

lemma verticalIntegral_split_three (a b : ℝ) (hf : Integrable (fun t : ℝ ↦ f (σ + t * I))) :
    VerticalIntegral f σ = I • (∫ t in Iic a, f (σ + t * I)) + I • (∫ t in a..b, f (σ + t * I))
    + I • ∫ t in Ici b, f (σ + t * I) := by
  simp_rw [VerticalIntegral, ← smul_add]
  congr
  rw [← intervalIntegral.integral_Iic_sub_Iic hf.restrict hf.restrict, add_sub_cancel'_right,
    integral_Iic_eq_integral_Iio, intervalIntegral.integral_Iio_add_Ici hf.restrict hf.restrict]

/-%%
\begin{lemma}[DiffVertRect_eq_UpperLowerUs]\label{DiffVertRect_eq_UpperLowerUs}\lean{DiffVertRect_eq_UpperLowerUs}\leanok
The difference of two vertical integrals and a rectangle is the difference of an upper and a lower U integrals.
\end{lemma}
%%-/
lemma DiffVertRect_eq_UpperLowerUs {f : ℂ → ℂ} {σ σ' T : ℝ}
    (f_int_σ : Integrable (fun (t : ℝ) ↦ f (σ + t * I)))
    (f_int_σ' : Integrable (fun (t : ℝ) ↦ f (σ' + t * I))) :
  (VerticalIntegral f σ') - (VerticalIntegral f σ) - (RectangleIntegral f (σ - I * T) (σ' + I * T)) = (UpperUIntegral f σ σ' T) - (LowerUIntegral f σ σ' T) := by
  rw[verticalIntegral_split_three (-T) T f_int_σ, verticalIntegral_split_three (-T) T f_int_σ',
    RectangleIntegral, UpperUIntegral, LowerUIntegral]
  norm_num
  have {a b c d e g h i : ℂ} :
    a + b + c - (d + e + g) - (h - i + b - e) = i + c - g - (h - a + d) := by ring
  convert this using 1

/-%%
\begin{proof}\uses{UpperUIntegral, LowerUIntegral}\leanok
Follows directly from the definitions.
\end{proof}
%%-/

/-- A function is `HolomorphicOn` a set if it is complex differentiable on that set. -/
abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop := DifferentiableOn ℂ f s

/-%%
\begin{theorem}[existsDifferentiableOn_of_bddAbove]\label{existsDifferentiableOn_of_bddAbove}\lean{existsDifferentiableOn_of_bddAbove}\leanok
If $f$ is differentiable on a set $s$ except at $c\in s$, and $f$ is bounded above on $s\setminus\{c\}$, then there exists a differentiable function $g$ on $s$ such that $f$ and $g$ agree on $s\setminus\{c\}$.
\end{theorem}
%%-/
theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E] {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c})) (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E), HolomorphicOn g s ∧ (Set.EqOn f g (s \ {c})) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim else by simp [h]⟩
/-%%
\begin{proof}\leanok
This is the Riemann Removable Singularity Theorem, slightly rephrased from what's in Mathlib. (We don't care what the function $g$ is, just that it's holomorphic.)
\end{proof}
%%-/

/-%%
\begin{theorem}[HolomorphicOn.vanishesOnRectangle]\label{HolomorphicOn.vanishesOnRectangle}\lean{HolomorphicOn.vanishesOnRectangle}\leanok
If $f$ is holomorphic on a rectangle $z$ and $w$, then the integral of $f$ over the rectangle with corners $z$ and $w$ is $0$.
\end{theorem}
%%-/
theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E] {U : Set ℂ}
    (f_holo : HolomorphicOn f U) (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w (f_holo.mono hU)
/-%%
\begin{proof}\leanok
This is in a Mathlib PR.
\end{proof}
%%-/

theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral
  congr 2; swap; congr 1; swap; congr 1
  all_goals refine intervalIntegral.integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩

theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]

theorem rectangleIntegral_symm (f : ℂ → E) (z w : ℂ) :
    RectangleIntegral f z w = RectangleIntegral f w z := by
  simp_rw [RectangleIntegral, intervalIntegral.integral_symm w.re,
    intervalIntegral.integral_symm w.im, sub_neg_eq_add, smul_neg, sub_neg_eq_add, ← sub_eq_add_neg,
    neg_add_eq_sub, sub_add_eq_add_sub]

theorem rectangleIntegral_symm_re (f : ℂ → ℂ) (z w : ℂ) :
    RectangleIntegral f (w.re + z.im * I) (z.re + w.im * I) = - RectangleIntegral f z w := by
  simp? [RectangleIntegral, intervalIntegral.integral_symm w.re] says
    simp only [RectangleIntegral._eq_1, add_im, ofReal_im, mul_im, ofReal_re, I_im,
      mul_one, I_re, mul_zero, add_zero, zero_add, add_re, mul_re, sub_self, smul_eq_mul,
      intervalIntegral.integral_symm w.re, sub_neg_eq_add, neg_sub]
  group

def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im

theorem RectangleBorderIntegrable.add {f g : ℂ → ℂ} (hf : RectangleBorderIntegrable f z w)
    (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral]
  rw [intervalIntegral.integral_add hf.1 hg.1, intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1, intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

theorem ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩

theorem ContinuousOn.rectangleBorderIntegrable (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  (hf.mono (rectangleBorder_subset_rectangle z w)).rectangleBorder_integrable

theorem ContinuousOn.rectangleBorderNoPIntegrable (hf : ContinuousOn f (Rectangle z w \ {p}))
    (pNotOnBorder : p ∉ RectangleBorder z w) : RectangleBorderIntegrable f z w := by
  refine (hf.mono (Set.subset_diff.mpr ?_)).rectangleBorder_integrable
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩

theorem HolomorphicOn.rectangleBorderIntegrable' (hf : HolomorphicOn f (Rectangle z w \ {p}))
    (hp : Rectangle z w ∈ nhds p) : RectangleBorderIntegrable f z w :=
  hf.continuousOn.rectangleBorderNoPIntegrable (not_mem_rectangleBorder_of_rectangle_mem_nhds hp)

theorem HolomorphicOn.rectangleBorderIntegrable (hf : HolomorphicOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  hf.continuousOn.rectangleBorderIntegrable

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
  dsimp [RectangleIntegral]
  simp only [mul_one, mul_zero, add_zero, zero_add, sub_self]
  rw [← intervalIntegral.integral_add_adjacent_intervals f_int_x₀_a_bot f_int_a_x₁_bot,
    ← intervalIntegral.integral_add_adjacent_intervals f_int_x₀_a_top f_int_a_x₁_top]
  abel

lemma RectangleIntegralHSplit' {a x₀ x₁ y₀ y₁ : ℝ} (ha : a ∈ [[x₀, x₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) :=
  RectangleIntegralHSplit
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)

lemma RectangleIntegralVSplit {f : ℂ → ℂ} {b x₀ x₁ y₀ y₁ : ℝ}
    (f_int_y₀_b_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume y₀ b)
    (f_int_b_y₁_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume b y₁)
    (f_int_y₀_b_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume y₀ b)
    (f_int_b_y₁_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume b y₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral]
  simp only [mul_one, mul_zero, add_zero, zero_add, sub_self]
  rw [← intervalIntegral.integral_add_adjacent_intervals f_int_y₀_b_left f_int_b_y₁_left,
    ← intervalIntegral.integral_add_adjacent_intervals f_int_y₀_b_right f_int_b_y₁_right]
  ring

lemma RectangleIntegralVSplit' {f : ℂ → ℂ} {b x₀ x₁ y₀ y₁ : ℝ} (hb : b ∈ [[y₀, y₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) :=
  RectangleIntegralVSplit
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)

lemma RectanglePullToNhdOfPole' {f : ℂ → ℂ} {z₀ z₁ z₂ z₃ p : ℂ}
    (h_orientation : z₀.re ≤ z₃.re ∧ z₀.im ≤ z₃.im ∧ z₁.re ≤ z₂.re ∧ z₁.im ≤ z₂.im)
    (hp : Rectangle z₁ z₂ ∈ 𝓝 p) (hz : Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃)
    (fHolo : HolomorphicOn f (Rectangle z₀ z₃ \ {p})) :
    RectangleIntegral f z₀ z₃ = RectangleIntegral f z₁ z₂ := by
  obtain ⟨hz₀_re, hz₀_im, hz₁_re, hz₁_im⟩ := h_orientation
  have := rect_subset_iff.mp hz
  rw [Rectangle, uIcc_of_le hz₀_re, uIcc_of_le hz₀_im] at this
  obtain ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := this
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ := (uIoo_of_le hz₁_re) ▸ (uIoo_of_le hz₁_im) ▸ rectangle_mem_nhds_iff.mp hp
  obtain ⟨_, _, _, _⟩ := show p.re < z₂.re ∧ p.re < z₃.re ∧ p.im < z₂.im ∧ p.im < z₃.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨_, _, _, _⟩ := show z₀.re < p.re ∧ z₁.re < p.re ∧ z₀.im < p.im ∧ z₁.im < p.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩

  have fCont := fHolo.continuousOn

  have hbot : RectangleBorderIntegrable f (↑z₀.re + ↑z₀.im * I) (↑z₃.re + ↑z₃.im * I) := ?_
  have htop : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I) (↑z₃.re + ↑z₃.im * I) := ?_
  have hleft : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I) (↑z₃.re + ↑z₂.im * I) := ?_
  have hright : RectangleBorderIntegrable f (↑z₁.re + ↑z₁.im * I) (↑z₃.re + ↑z₂.im * I) := ?_
  all_goals try {
    refine (fCont.mono (rectangleBorder_subset_punctured_rect ?_ ?_)).rectangleBorder_integrable
    · simp_all
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith⟩
  }
  have hbot' : z₁.im ∈ [[z₀.im, z₃.im]] := ?_
  have htop' : z₂.im ∈ [[z₁.im, z₃.im]] := ?_
  have hleft' : z₁.re ∈ [[z₀.re, z₃.re]] := ?_
  have hright' : z₂.re ∈ [[z₁.re, z₃.re]] := ?_
  all_goals try { rw [Set.uIcc_of_le]; constructor; all_goals assumption }
  have hbot'' : Rectangle (↑z₀.re + ↑z₀.im * I) (↑z₃.re + ↑z₁.im * I) ⊆ Rectangle z₀ z₃ \ {p} := ?_
  have htop'' : Rectangle (↑z₀.re + ↑z₂.im * I) (↑z₃.re + ↑z₃.im * I) ⊆ Rectangle z₀ z₃ \ {p} := ?_
  have hleft'' : Rectangle (↑z₀.re + ↑z₁.im * I) (↑z₁.re + ↑z₂.im * I) ⊆ Rectangle z₀ z₃ \ {p} := ?_
  have hright'' : Rectangle (↑z₂.re + ↑z₁.im * I) (↑z₃.re + ↑z₂.im * I) ⊆ Rectangle z₀ z₃ \ {p} := ?_
  all_goals try { apply rectangle_subset_punctured_rect <;> simp_all }

  rw [← re_add_im z₀, ← re_add_im z₃,
    RectangleIntegralVSplit' hbot' hbot, fHolo.vanishesOnRectangle hbot'', zero_add,
    RectangleIntegralVSplit' htop' htop, fHolo.vanishesOnRectangle htop'', add_zero,
    RectangleIntegralHSplit' hleft' hleft, fHolo.vanishesOnRectangle hleft'', zero_add,
    RectangleIntegralHSplit' hright' hright, fHolo.vanishesOnRectangle hright'', add_zero,
    re_add_im, re_add_im]

/-%%
The next lemma allows to zoom a big rectangle down to a small square, centered at a pole.

\begin{lemma}[RectanglePullToNhdOfPole]\label{RectanglePullToNhdOfPole}\lean{RectanglePullToNhdOfPole}\leanok
If $f$ is holomorphic on a rectangle $z$ and $w$ except at a point $p$, then the integral of $f$
over the rectangle with corners $z$ and $w$ is the same as the integral of $f$ over a small square
centered at $p$.
\end{lemma}
%%-/
/-- Given `f` holomorphic on a rectangle `z` and `w` except at a point `p`, the integral of `f` over
the rectangle with corners `z` and `w` is the same as the integral of `f` over a small square
centered at `p`. -/
lemma RectanglePullToNhdOfPole {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re ≤ w.re)
    (zIm_lt_wIm : z.im ≤ w.im) (hp : Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0,
    RectangleIntegral f z w = RectangleIntegral f (-c - I * c + p) (c + I * c + p) := by
/-%%
\begin{proof}\uses{HolomorphicOn.vanishesOnRectangle}\leanok
Chop the big rectangle with two vertical cuts and two horizontal cuts into smaller rectangles,
the middle one being the desired square. The integral over each of the outer rectangles
vanishes, since $f$ is holomorphic there. (The constant $c$ being ``small enough'' here just means
that the inner square is strictly contained in the big rectangle.)
%%-/
  filter_upwards [Ioo_mem_nhdsWithin_Ioi' zero_lt_one, SmallSquareInRectangle hp]
  intro c ⟨cpos, _⟩ hc
  simp_rw [mul_comm I]
  exact RectanglePullToNhdOfPole' (by simp_all [cpos.le])
    (square_mem_nhds p (ne_of_gt cpos)) hc fHolo
--%%\end{proof}

lemma RectanglePullToNhdOfPole'' {f : ℂ → ℂ} {z w p : ℂ} (zRe_le_wRe : z.re ≤ w.re)
    (zIm_le_wIm : z.im ≤ w.im) (pInRectInterior : Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0,
    RectangleIntegral' f z w = RectangleIntegral' f (-c - I * c + p) (c + I * c + p) := by
  filter_upwards [RectanglePullToNhdOfPole zRe_le_wRe zIm_le_wIm pInRectInterior fHolo] with c h
  simp_rw [RectangleIntegral', h]

theorem ResidueTheoremAtOrigin_aux1a :
    ∫ (x : ℝ) in (-1)..1, ((1 + x ^ 2)⁻¹ : ℂ) = ↑(arctan 1) - ↑(arctan (-1)) := by
  norm_cast
  rw [intervalIntegral.integral_ofReal, integral_inv_one_add_sq]

theorem ResidueTheoremAtOrigin_aux1b (x : ℝ) :
    (x + -I)⁻¹ - (x + I)⁻¹ = (2 * I) * ↑((1 + x ^ 2)⁻¹ : ℝ) := by
  have hu₁ : IsUnit (x + -I) := Ne.isUnit (by simp [Complex.ext_iff])
  have hu₂ : IsUnit (x + I) := Ne.isUnit (by simp [Complex.ext_iff])
  apply hu₁.mul_left_cancel
  rw [mul_sub, hu₁.mul_inv_cancel]
  apply hu₂.mul_left_cancel
  calc
    _ = (x + I) * 1 - (x + I)⁻¹ * (x + I) * (x + -I) := by group
    _ = (1 : ℝ) * (2 * I) := by simp [hu₂.inv_mul_cancel, two_mul]
    _ = ((1 + x ^ 2)⁻¹ * (1 + x ^ 2) : ℝ) * (2 * I) := by
      congr 2
      exact (Ne.isUnit (by nlinarith)).inv_mul_cancel.symm
    _ = ((1 + x ^ 2 : ℂ)⁻¹ * ((x + I) * (x + -I))) * (2 * I) := by
      push_cast
      congr 2
      trans - I ^ 2 + x ^ 2; simp; group
    _ = _ := by norm_cast; group

theorem ResidueTheoremAtOrigin_aux1c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (y + I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop) (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux1c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (↑y + -I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop) (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux1 :
    (∫ (x : ℝ) in (-1 - 0)..(1 + 0), 1 / (x + (-0 - 1 : ℝ) * I)) -
    ∫ (x : ℝ) in (-1 - 0)..(1 + 0), 1 / (x + (0 + 1 : ℝ) * I) = π * I := by
  suffices (∫ (x : ℝ) in (-1 : ℝ)..1, (x + -I)⁻¹) - ∫ (x : ℝ) in (-1 : ℝ)..1, (x + I)⁻¹ = π * I by
    simpa
  rw [← intervalIntegral.integral_sub
    (ResidueTheoremAtOrigin_aux1c' (-1) 1) (ResidueTheoremAtOrigin_aux1c (-1) 1)]
  trans 2 * I * (π / 4 + π / 4)
  · simp [ResidueTheoremAtOrigin_aux1b, ResidueTheoremAtOrigin_aux1a]
  · group

theorem ResidueTheoremAtOrigin_aux2b (y : ℝ) :
    (1 + y * I)⁻¹ - (-1 + y * I)⁻¹ = 2 * ((1 + y ^ 2)⁻¹ : ℝ) := by
  have hu₁ : IsUnit (1 + y * I) := Ne.isUnit (by simp [Complex.ext_iff])
  have hu₂ : IsUnit (-1 + y * I) := Ne.isUnit (by simp [Complex.ext_iff])
  apply hu₁.mul_left_cancel
  rw [mul_sub, hu₁.mul_inv_cancel]
  apply hu₂.mul_left_cancel
  calc
    _ = (-1 + ↑y * I) * 1 - (-1 + ↑y * I)⁻¹ * (-1 + ↑y * I) * (1 + ↑y * I) := by group
    _ = ((1 * -2) : ℝ) := by trans -1 - 1; simp [hu₂.inv_mul_cancel]; norm_num
    _ = (((1 + y ^ 2)⁻¹ * (1 + y ^ 2) : ℝ) * (-2) : ℝ) := by
      congr 2
      exact (Ne.isUnit (by nlinarith)).inv_mul_cancel.symm
    _ = (1 + (y : ℂ) ^ 2)⁻¹ * (1 + (y : ℂ) ^ 2) * (-2) := by norm_cast
    _ = (1 + (y : ℂ) ^ 2)⁻¹ * (-(1 + y * I) * (-1 + y * I)) * (-2) := by
      congr 2
      trans 1 - ↑y ^ 2 * I ^ 2; simp; group
    _ = _ := by push_cast; group

theorem ResidueTheoremAtOrigin_aux2c (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (1 + ↑y * I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop) (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux2c' (a b : ℝ) :
    let f : ℝ → ℂ := fun y => (-1 + ↑y * I)⁻¹
    IntervalIntegrable f volume a b :=
  (ContinuousOn.inv₀ (by fun_prop) (by simp [Complex.ext_iff])).intervalIntegrable

theorem ResidueTheoremAtOrigin_aux2 :
    (I * ∫ (y : ℝ) in (-0 - 1)..0 + 1, 1 / ((1 + 0 : ℝ) + y * I)) -
    I * ∫ (y : ℝ) in (-0 - 1)..0 + 1, 1 / ((-1 - 0 : ℝ) + y * I) = π * I := by
  rw [← mul_sub, mul_comm (π : ℂ) I]
  suffices (∫ y in (-1 : ℝ)..1, (1 + ↑y * I)⁻¹) - ∫ y in (-1 : ℝ)..1, (-1 + ↑y * I)⁻¹ = ↑π by simpa
  rw [← intervalIntegral.integral_sub
    (ResidueTheoremAtOrigin_aux2c (-1) 1) (ResidueTheoremAtOrigin_aux2c' (-1) 1)]
  trans 2 * (↑π / 4 + ↑π / 4)
  · simp [ResidueTheoremAtOrigin_aux2b, ResidueTheoremAtOrigin_aux1a]
  · group

/-%%
\begin{lemma}[ResidueTheoremAtOrigin]\label{ResidueTheoremAtOrigin}
\lean{ResidueTheoremAtOrigin}\leanok
The rectangle (square) integral of $f(s) = 1/s$ with corners $-1-i$ and $1+i$ is equal to $2\pi i$.
\end{lemma}
%%-/
lemma ResidueTheoremAtOrigin :
    RectangleIntegral' (fun s ↦ 1 / s) (-1 - I) (1 + I) = 1 := by
  dsimp [RectangleIntegral', RectangleIntegral]
  rw [ResidueTheoremAtOrigin_aux1, add_sub_assoc, ResidueTheoremAtOrigin_aux2]
  trans  1 / (2 * ↑π * I) * (2 * ↑π * I)
  · group
  · exact one_div_mul_cancel (by norm_num; exact pi_ne_zero)
/-%%
\begin{proof}\leanok
The bottom is:
$$
\frac1{2\pi i}
\int_{-1-i}^{1-i} \frac1z dz
=
\frac1{2\pi i}
\int_{-1}^1 \frac1{x-i} dx,
$$
and the top is the negative of:
$$
\frac1{2\pi i}
\int_{-1+i}^{1+i} \frac1z dz
=
\frac1{2\pi i}
\int_{-1}^1 \frac1{x+i} dx.
$$
The two together add up to:
$$
\frac1{2\pi i}
\int_{-1}^1
\left(\frac1{x-i}-\frac1{x+i} \right)dx
=
\frac1{\pi}
\int_{-1}^1
\frac{1}{x^2+1}dx,
$$
which is the arctan at $1$ (namely $\pi/4$) minus that at $-1$. In total, this contributes $1/2$ to the integral.

The vertical sides are:
$$
\frac1{2\pi i}
\int_{1-i}^{1+i} \frac1z dz
=
\frac1{2\pi}
\int_{-1}^1 \frac1{1+iy} dy
$$
and the negative of
$$
\frac1{2\pi i}
\int_{-1-i}^{-1+i} \frac1z dz
=
\frac1{2\pi}
\int_{-1}^1 \frac1{-1+iy} dy.
$$
This difference comes out to:
$$
\frac1{2\pi}
\int_{-1}^1 \left(\frac1{1+iy}-\frac1{-1+iy}\right) dy
=
\frac1{2\pi}
\int_{-1}^1 \left(\frac{-2}{-1-y^2}\right) dy,
$$
which contributes another factor of $1/2$. (Fun! Each of the vertical/horizontal sides contributes half of the winding.)
\end{proof}
%%-/

theorem RectangleIntegral.const_mul (f : ℂ → ℂ) (z w c : ℂ) :
    RectangleIntegral (fun s => c * f s) z w = c * RectangleIntegral f z w := by
  simpa [RectangleIntegral] using by ring

theorem RectangleIntegral.const_mul' (f : ℂ → ℂ) (z w c : ℂ) :
    RectangleIntegral' (fun s => c * f s) z w = c * RectangleIntegral' f z w := by
  simpa [RectangleIntegral', RectangleIntegral.const_mul] using by ring

theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, sub_re, sub_im, ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]

theorem RectangleIntegral.translate' (f : ℂ → ℂ) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]

lemma Complex.inv_re_add_im : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv] ; congr <;> simp [conj_ofReal, normSq] <;> ring

lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by linarith [sq_nonneg x, (sq_pos_iff y).mpr hy]

lemma continuous_self_div_sq_add_sq (hy : y ≠ 0) : Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (λ _ => sq_add_sq_ne_zero hy)

lemma integral_self_div_sq_add_sq (hy : y ≠ 0) : ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (by simpa using hasDerivAt_pow 2 x) (y ^ 2)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1 ; field_simp ; ring
  have e3 : deriv f = λ x => x / (x ^ 2 + y ^ 2) := funext (λ _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (λ _ _ => e2.differentiableAt) <| e4.intervalIntegrable _ _

lemma integral_const_div_sq_add_sq (hy : y ≠ 0) : ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) =
    arctan (x₂ / y) - arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel x₁ hy, ← div_mul_cancel x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← integral_const_mul, ← integral_one_div_one_add_sq]
  refine integral_congr <| λ x _ => ?_
  field_simp ; ring

lemma integral_const_div_self_add_im (hy : y ≠ 0) : ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (arctan (x₂ / y) - arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf ; simp_rw [inv_re_add_im] ; ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc] ; norm_cast
    exact continuous_const.mul <| continuous_ofReal.comp <| continuous_self_div_sq_add_sq hy
  have e3 : IntervalIntegrable (fun x ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by continuity) (λ x => ?_)
    norm_cast ; exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (λ _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [integral_const_mul, intervalIntegral.integral_ofReal, integral_self_div_sq_add_sq hy,
    integral_const_div_sq_add_sq hy]

lemma integral_const_div_re_add_self (hx : x ≠ 0) : ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (arctan (y₂ / -x) - arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : x + y * I ≠ 0 := by contrapose! hx ; simpa using congr_arg re hx
    have e2 : y + -(x * I) ≠ 0 := by contrapose! hx ; simpa using congr_arg im hx
    field_simp ; ring_nf ; simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]

lemma ResidueTheoremAtOrigin' {z w c : ℂ} (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (λ s => c / s) z w = 2 * I * π * c := by
  simp only [RectangleIntegral._eq_1, smul_eq_mul]
  rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
  rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, one_mul, neg_neg, arctan_neg, ofReal_neg, sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf

theorem ResidueTheoremInRectangle (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) : RectangleIntegral' (λ s => c / (s - p)) z w = c := by
  simp [rectangle_mem_nhds_iff, mem_reProdIm, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm]
    at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * I) * (2 * I * ↑π * c) = c := by field_simp [two_pi_I_ne_zero] ; ring
  rwa [ResidueTheoremAtOrigin'] ; all_goals { simp [*] }

/-%%
\begin{lemma}[ResidueTheoremOnRectangleWithSimplePole]\label{ResidueTheoremOnRectangleWithSimplePole}
\lean{ResidueTheoremOnRectangleWithSimplePole}\leanok
Suppose that $f$ is a holomorphic function on a rectangle, except for a simple pole
at $p$. By the latter, we mean that there is a function $g$ holomorphic on the rectangle such that, $f = g + A/(s-p)$ for some $A\in\C$. Then the integral of $f$ over the
rectangle is $A$.
\end{lemma}
%%-/
lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p)
    (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) (g) (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by

  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (Rectangle z w \ {p}) := by
    intro s hs
    simp [← principalPart hs]

  have : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder z w) :=
    principalPart'.mono <| Set.subset_diff.mpr ⟨rectangleBorder_subset_rectangle z w,
      disjoint_singleton_right.mpr (not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior)⟩
  rw [RectangleIntegral'_congr this]

  have t1 : RectangleBorderIntegrable g z w := gHolo.rectangleBorderIntegrable
  have t2 : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · intro x hx
        rw [sub_ne_zero]
        exact hx
    · rintro s ⟨_, hs⟩ ; exact hs
  have t3 : RectangleBorderIntegrable (fun s ↦ A / (s - p)) z w :=
    HolomorphicOn.rectangleBorderIntegrable' t2 pInRectInterior

  rw [RectangleIntegral', RectangleBorderIntegrable.add t1 t3, smul_add]
  rw [gHolo.vanishesOnRectangle (by rfl), smul_zero, zero_add]

  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior

/-%%
\begin{proof}
\uses{ResidueTheoremAtOrigin, RectanglePullToNhdOfPole, HolomorphicOn.vanishesOnRectangle}
\leanok
Replace $f$ with $g + A/(s-p)$ in the integral.
The integral of $g$ vanishes by Lemma \ref{HolomorphicOn.vanishesOnRectangle}.
 To evaluate the integral of $1/(s-p)$,
pull everything to a square about the origin using Lemma \ref{RectanglePullToNhdOfPole},
and rescale by $c$;
what remains is handled by Lemma \ref{ResidueTheoremAtOrigin}.
\end{proof}
%%-/

-- theorem nhds_basis_square (p : ℂ) : HasBasis (𝓝 p) (0 < ·) (Square p ·) := by
--   apply Filter.HasBasis.to_hasBasis' Metric.nhds_basis_closedBall <;> intro c hc
--   · refine ⟨c / Real.sqrt 2, div_pos hc (Real.sqrt_pos.mpr zero_lt_two), ?_⟩
--     convert square_subset_closedBall p (c / Real.sqrt 2)
--     field_simp [abs_div, abs_eq_self.mpr hc.le, abs_eq_self.mpr (sqrt_nonneg 2)]
--   · refine square_mem_nhds _ hc.ne.symm
