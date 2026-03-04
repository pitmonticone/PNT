import Mathlib

/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Maksym Radziwill
-/
/-- Given a complex function $f$, we define the function
    $$g(z):=\begin{cases}
    \frac{f(z)}{z}, & z\neq 0;\\
    f'(0), & z=0.
    \end{cases}$$
-/
noncomputable abbrev divRemovable_zero (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ (f z) / z) 0 ((deriv f) 0)

-- Away from zero divRemovable_zero f z is equal to f z / z
/-- Let $f$ be a complex function and let $z\neq 0$. Then, with $g$ defined as in
    Definition~\ref{divRemovable_zero},
    $$g(z)=\frac{f(z)}{z}.$$

PROVIDED SOLUTION:
This follows directly from the definition of $g$.
-/
lemma divRemovable_zero_of_ne_zero {z : ℂ} (f : ℂ → ℂ) (z_ne_0 : z ≠ 0) :
    divRemovable_zero f z = f z / z := by
  admit

-- If f is analytic on an open set and f 0 = 0 then f z / z is also
-- analytic on the same open set.
/-- Let $f$ be a complex function analytic on an open set $s$ containing $0$ such that $f(0)=0$.
    Then, with $g$ defined as in Definition~\ref{divRemovable_zero}, $g$ is analytic on $s$.

PROVIDED SOLUTION:
We need to show that $g$ is complex differentiable at every point in $s$.
    For $z\neq 0$, this follows directly from the definition of $g$ and the fact that $f$ is
    analytic on $s$. For $z=0$, we use the definition of the derivative and the fact that
    $f(0)=0$:
    $$
    \lim_{z\to 0}\frac{g(z)-g(0)}{z-0}=\lim_{z\to 0}\frac{\frac{f(z)}{z}-f'(0)}{z}
    =\lim_{z\to 0}\frac{f(z)-f'(0)z}{z^2}
    =\lim_{z\to 0}\frac{f(z)-f(0)-f'(0)(z-0)}{(z-0)^2}=0,
    $$
    where the last equality follows from the definition of the derivative of $f$ at $0$.
    Thus, $g$ is complex differentiable at $0$ with derivative $0$, completing the proof.
-/
lemma AnalyticOn_divRemovable_zero {f : ℂ → ℂ} {s : Set ℂ}
    (sInNhds0 : s ∈ nhds 0) (zero : f 0 = 0) (o : IsOpen s)
    (analytic : AnalyticOn ℂ f s) : AnalyticOn ℂ (divRemovable_zero f) s := by
  admit

-- The proof of the Lemma below is cumbersome, a proper way would be to
-- show that if f is analytic on a closed set C, then it is analytic on an
-- open set O containing the closed set C and apply the previous lemma.
/-- Let $f$ be a complex function analytic on the closed ball $|z|\leq R$ such that $f(0)=0$.
    Then, with $g$ defined as in Definition~\ref{divRemovable_zero}, $g$ is analytic on
    $|z|\leq R$.

PROVIDED SOLUTION:
The proof is similar to that of Lemma~\ref{AnalyticOn_divRemovable_zero}, but we need to
    consider two cases: when $x$ is on the boundary of the closed ball and when it is in the
    interior.
    In the first case, we take a small open ball around $x$ that lies entirely within the
    closed ball, and apply Lemma~\ref{AnalyticOn_divRemovable_zero} on this smaller ball.
    In the second case, we can take the entire open ball centered at $0$ with radius $R$,
    and again apply Lemma~\ref{AnalyticOn_divRemovable_zero}.
    In both cases, we use the fact that $f(0)=0$ to ensure that the removable singularity at
    $0$ is handled correctly.
-/
lemma AnalyticOn_divRemovable_zero_closedBall {f : ℂ → ℂ} {R : ℝ}
    (Rpos : 0 < R) (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zero : f 0 = 0) : AnalyticOn ℂ (divRemovable_zero f) (Metric.closedBall 0 R) := by
  admit

/-- Given a complex function $f$ and a real number $M$, we define the function
    $$f_{M}(z):=\frac{g(z)}{2M - f(z)},$$
    where $g$ is defined as in Definition~\ref{divRemovable_zero}.
-/
noncomputable abbrev schwartzQuotient (f : ℂ → ℂ) (M : ℝ) : ℂ → ℂ :=
  fun z ↦ (divRemovable_zero f z) / (2 * M - f z)

-- AnalyticOn.schwartzQuotient establishes that f_{M}(z) is analytic.
/-- Let $M>0$. Let $f$ be analytic on the closed ball $|z|\leq R$ such that $f(0)=0$
    and suppose that $2M - f(z)\neq 0$ for all $|z|\leq R$.
    Then, with $f_{M}$ defined as in Definition~\ref{schwartzQuotient}, $f_{M}$ is analytic on
    $|z|\leq R$.

PROVIDED SOLUTION:
This follows directly from Lemma~\ref{AnalyticOn_divRemovable_zero_closedBall} and the fact
    that the difference of two analytic functions is analytic.
-/
lemma AnalyticOn.schwartzQuotient {f : ℂ → ℂ} {R : ℝ} (M : ℝ)
    (Rpos : 0 < R) (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (nonzero : ∀ z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0)
    (zero : f 0 = 0) : AnalyticOn ℂ (schwartzQuotient f M) (Metric.closedBall 0 R) := by
  admit

-- If Re x ≤ M then |x| ≤ |2 * M - x|, this simple inequality is used
-- in the proof of borelCaratheodory_closedBall.
/-- Let $M>0$ and let $x$ be a complex number such that $\Re x\leq M$.
    Then, $|x|\leq|2M - x|$.

PROVIDED SOLUTION:
We square both sides and simplify to obtain the equivalent inequality
    $$0\leq 4M^2 -4M\Re x,$$
    which follows directly from the assumption $\Re x\leq M$ and the positivity of $M$.
-/
lemma Complex.norm_le_norm_two_mul_sub_of_re_le {M : ℝ} {x : ℂ}
    (Mpos : 0 < M) (hyp_re_x : x.re ≤ M) : ‖x‖ ≤ ‖2 * M - x‖ := by
  admit

-- This is a version of the maximum modulus principle specialized to closed balls.

lemma AnalyticOn.norm_le_of_norm_le_on_sphere {f : ℂ → ℂ} {C R r : ℝ}
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (hyp_r : r ≤ R) (cond : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C)
    (w : ℂ) (wInS : w ∈ Metric.closedBall 0 r) : ‖f w‖ ≤ C := by
  admit

-- We can now prove Borel-Caratheodory for closed balls
/-- **borelCaratheodory-closedBall**

Let $R,\,M>0$. Let $f$ be analytic on $|z|\leq R$ such that $f(0)=0$ and suppose
    $\Re f(z)\leq M$ for all $|z|\leq R$. Then for any $0 < r < R$,
    $$\sup_{|z|\leq r}|f(z)|\leq\frac{2Mr}{R-r}.$$

PROVIDED SOLUTION:
Let
    $$f_M(z)=\frac{f(z)/z}{2M-f(z)}.$$
    Note that $2M-f(z)\neq 0$ because $\Re (2M-f(z))=2M-\Re f(z)\geq M>0$. Additionally, since
    $f(z)$ has a zero at $0$, we know that $f(z)/z$ is analytic on $|z|\leq R$. Likewise,
    $f_M(z)$ is analytic on $|z|\leq R$.

    Now note that $|f(z)|\leq|2M-f(z)|$ since $\Re f(z)\leq M$. Thus we have that
    $$|f_M(z)|=\frac{|f(z)|/|z|}{|2M-f(z)|}\leq\frac{1}{|z|}.$$
    Now by the maximum modulus principle, we know the maximum of $|f_M|$ must occur on the
    boundary where $|z|=R$. Thus, $|f_M(z)|\leq 1/R$ for all $|z|\leq R$. So for $|z|=r$ we have
    $$|f_M(z)|=\frac{|f(z)|/r}{|2M-f(z)|}\leq\frac{1}{R}\implies R\,|f(z)|\leq r\,|2M-f(z)|\leq
    2Mr+r\,|f(z)|.$$
    Which by algebraic manipulation gives
    $$|f(z)|\leq\frac{2Mr}{R-r}.$$
    Once more, by the maximum modulus principle, we know the maximum of $|f|$ must occur on the
    boundary where $|z|=r$. Thus, the desired result immediately follows
-/
theorem borelCaratheodory_closedBall {M R r : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (Rpos : 0 < R) (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zeroAtZero : f 0 = 0) (Mpos : 0 < M)
    (realPartBounded : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
    (hyp_r : r < R) (hyp_z : z ∈ Metric.closedBall 0 r)
    : ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  admit