import Mathlib
import PrimeNumberTheoremAnd.ConsequencesAristotle
import PrimeNumberTheoremAnd.PrimaryDefinitionsAristotle
import PrimeNumberTheoremAnd.Li2BoundsAristotle

/-!
# Definitions
-/

/-!
In this section we define the basic types of secondary estimates we will work with in the project.
-/

open Real Finset Topology
/-- **Log upper bound**

For $t > -1$, one has $\log (1+t) \leq t$.

PROVIDED SOLUTION:
This follows from the mean value theorem.
-/
theorem log_le (t : ℝ) (ht : t > -1) : log (1 + t) ≤ t := by
  admit

/-- **First log lower bound**

For $t \geq 0$, one has $t - \frac{t^2}{2} \leq \log(1+t)$.

PROVIDED SOLUTION:
Use Taylor's theorem with remainder and the fact that the second derivative of $\log(1+t)$ is at most $1$ for $t \geq 0$.
-/
theorem log_ge {t : ℝ} (ht : 0 ≤ t) : t - t ^ 2 / 2 ≤ log (1 + t) := by
  admit

/-- **Second log lower bound**

For $0 \leq t \leq t_0 < 1$, one has $\frac{t}{t_0} \log (1-t_0) \leq \log(1-t)$.

PROVIDED SOLUTION:
Use concavity of log.
-/
theorem log_ge' {t t₀ : ℝ} (ht : 0 ≤ t) (ht0 : t ≤ t₀) (ht0' : t₀ < 1) :
    (t / t₀) * log (1 - t₀) ≤ log (1 - t) := by
  admit

/-- **Symmetrization of inverse log**

For $0 < t \leq 1/2$, one has $| \frac{1}{\log(1+t)} + \frac{1}{\log(1-t)}| \leq \frac{16\log(4/3)}{3}$.

PROVIDED SOLUTION:
The expression can be written as $\frac{|\log(1-t^2)|}{|\log(1-t)| |\log(1+t)|}$. Now use the previous upper and lower bounds, noting that $t^2 \leq 1/4$. NOTE: this gives the slightly weaker bound of $16 \log(4/3) / 3$, but this can suffice for applications.  The sharp bound would require showing that the left-hand side is monotone in $t$, which looks true but not so easy to verify.
-/
theorem symm_inv_log
    (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    |1 / log (1 + t) + 1 / log (1 - t)| ≤ 16 * log (4 / 3) / 3 := by
  admit

/-- **li minus Li**

$\li(x) - \Li(x) = \li(2)$.

PROVIDED SOLUTION:
This follows from the previous estimate.
-/
theorem li.sub_Li
    (x : ℝ) (h2x : 2 ≤ x) :
    li x - Li x = li 2 := by
  admit

/-- **Ramanujan-Soldner constant**

$\li(2) = 1.0451\dots$.

PROVIDED SOLUTION:
Symmetrize the integral and use and some numerical integration.
-/
theorem li.two_approx : li 2 ∈ Set.Icc 1.0451 1.0452 := by
  sorry


/-- The local li definition matches Li2Bounds.li (they are definitionally equal). -/
theorem li_eq_Li2Bounds_li (x : ℝ) : li x = Li2Bounds.li x := by
  admit

/-- **Weak bounds on li(2)**

$1.039 \leq \li(2) \leq 1.06$.
-/
theorem li.two_approx_weak : li 2 ∈ Set.Icc 1.039 1.06 := by
  admit

/-- **Symmetric form equals principal value**

$\int_0^1 \left(\frac{1}{\log(1+t)} + \frac{1}{\log(1-t)}\right) dt = \mathrm{li}(2)$
-/
theorem li2_symmetric_eq_li2 : Li2Bounds.li2_symmetric = li 2 := by
  admit