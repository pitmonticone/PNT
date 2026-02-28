import Mathlib
import PrimeNumberTheoremAnd.SecondaryDefinitionsAristotle
import PrimeNumberTheoremAnd.FioriKadiriSwidinskyAristotle
import PrimeNumberTheoremAnd.BKLNWAristotle
import PrimeNumberTheoremAnd.RosserSchoenfeldPrimeAristotle

/-!
# The implications of FKS2



In this file we record the implications in the paper [reference].  Roughly speaking, this paper has two components: a "$\psi$ to $\theta$ pipeline" that converts estimates on the error $E_\psi(x) = |\psi(x)-x|/x$ in the prime number theorem for the first Chebyshev function $\psi$ to estimates on the error $E_\theta(x) = |\theta(x)-x|/x$ in the prime number theorem for the second Chebyshev function $\theta$; and a "$\theta$ to $\pi$ pipeline" that converts estimates $E_\theta$ to estimates on the error $E_\pi(x) = |\pi(x) - \Li(x)|/(x/\log x)$ in the prime number theorem for the prime counting function $\pi$.  Each pipeline converts "admissible classical bounds" (Definitions \ref{classical-bound-psi} \ref{classical-bound-theta}, \ref{classical-bound-pi}) of one error to admissible classical bounds of the next error in the pipeline.

There are two types of bounds considered here.  The first are asymptotic bounds of the form
$$ E_\psi(x), E_\theta(x), E_\pi(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right) $$
for various $A,B,C,R$ and all $x \geq x_0$.  The second are numerical bounds of the form
$$ E_\psi(x), E_\theta(x), E_\pi(x) \leq \varepsilon_{num}(x_0) $$
for all $x \geq x_0$ and certain specific numerical choices of $x_0$ and $\varepsilon_{num}(x_0)$.  One needs to merge these bounds together to obtain the best final results.
-/

open Real MeasureTheory Chebyshev

namespace FKS2

/-!
## Basic estimates on the error bound g

Our asymptotic bounds can be described using a certain function $g$.  Here we define $g$ and record its basic properties.
-/
/-- **g function, FKS2 (16)**

For any $a,b,c,x \in \mathbb{R}$ we define
  $g(a,b,c,x) := x^{-a} (\log x)^b \exp( c (\log x)^{1/2} )$.
-/
noncomputable def g_bound (a b c x : ℝ) : ℝ := x^(-a) * (log x)^b * exp (c * sqrt (log x))
/-- **FKS2 Sublemma 10-1**

We have
$$ \frac{d}{dx} g(a, b, c, x) = \left( -a \log(x) + b + \frac{c}{2}\sqrt{\log(x)} \right) x^{-a-1} (\log(x))^{b-1} \exp(c\sqrt{\log(x)}).$$

PROVIDED SOLUTION:
This follows from straightforward differentiation.
-/
theorem lemma_10_substep {a b c x : ℝ} (hx : x > 1) :
  deriv (g_bound a b c) x =
    (-a * log x + b + (c / 2) * sqrt (log x)) * x ^ (-a - 1) * (log x) ^ (b - 1) * exp (c * sqrt (log x)) := by
  admit

/-- **FKS2 Sublemma 10-2**

$\frac{d}{dx} g(a, b, c, x) $ is negative when $-au^2 + \frac{c}{2}u + b < 0$, where $u = \sqrt{\log(x)}$.

PROVIDED SOLUTION:
Clear from previous sublemma.
-/
theorem lemma_10_substep_2 {a b c x : ℝ} (hx : x > 1) :
  deriv (g_bound a b c) x < 0 ↔
    -a * (sqrt (log x)) ^ 2 + (c / 2) * sqrt (log x) + b < 0 := by
  admit

/-- **FKS2 Lemma 10a**

If $a>0$, $c>0$ and $b < -c^2/16a$, then $g(a,b,c,x)$ decreases with $x$.

PROVIDED SOLUTION:
We apply Lemma \ref{fks2-lemma-10-substep-2}. There are no roots when $b < -\frac{c^2}{16a}$, and the derivative is always negative in this case.
-/
theorem lemma_10a {a b c : ℝ} (ha : a > 0) (hb : b < -c ^ 2 / (16 * a)) :
    StrictAntiOn (g_bound a b c) (Set.Ioi 1) := by
  admit

/-- **FKS2 Lemma 10b**

For any $a>0$, $c>0$ and $b \geq -c^2/16a$, $g(a,b,c,x)$ decreases with $x$ for
  $x > \exp((\frac{c}{4a} + \frac{1}{2a} \sqrt{\frac{c^2}{4} + 4ab})^2)$.

PROVIDED SOLUTION:
We apply Lemma \ref{fks2-lemma-10-substep-2}. If $a > 0$, there are two real roots only if $\frac{c^2}{4} + 4ab \geq 0$ or equivalently $b \geq -\frac{c^2}{16a}$, and the derivative is negative for $u > \frac{\frac{c}{2} + \sqrt{\frac{c^2}{4} + 4ab}}{2a}$.
-/
theorem lemma_10b {a b c : ℝ} (ha : a > 0) (hc : c > 0) (hb : b ≥ -c ^ 2 / (16 * a)) :
    StrictAntiOn (g_bound a b c) (Set.Ioi (exp ((c / (4 * a) + (1 / (2 * a)) * sqrt (c ^ 2 / 4 + 4 * a * b)) ^ 2))) := by
  admit

/-- **FKS2 Lemma 10c**

If $c>0$, $g(0,b,c,x)$ decreases with $x$ for $\sqrt{\log x} < -2b/c$.

PROVIDED SOLUTION:
We apply Lemma \ref{fks2-lemma-10-substep-2}. If $a = 0$, it is negative when $u < \frac{-2b}{c}$.
  Note: this lemma is mistyped as $\sqrt{\log x} > -2b/c$ in [reference].
-/
theorem lemma_10c {b c : ℝ} (hb : b < 0) (hc : c > 0) :
    StrictAntiOn (g_bound 0 b c) (Set.Ioo 1 (exp ((-2 * b / c) ^ 2))) := by
  admit

/-- **FKS2 Corollary 11**

If $B \geq 1 + C^2 / 16R$ then $g(1,1-B,C/\sqrt{R},x)$ is decreasing in $x$.

PROVIDED SOLUTION:
This follows from Lemma \ref{fks2-lemma-10a} applied with $a=1$, $b=1-B$ and $c=C/\sqrt{R}$.
-/
theorem corollary_11 {B C R : ℝ} (hR : R > 0) (hB : B > 1 + C ^ 2 / (16 * R)) :
    StrictAntiOn (g_bound 1 (1 - B) (C / sqrt R)) (Set.Ioi 1) := by
  admit

/-!
When integrating expressions involving $g$, the Dawson function naturally appears; and we need to record some basic properties about it.
-/
/-- **Dawson function, FKS2 (19)**

The Dawson function $D_+ : \mathbb{R} \to \mathbb{R}$ is defined by the formula
  $D_+(x) := e^{-x^2} \int_0^x e^{t^2}\ dt$.
-/
noncomputable def dawson (x : ℝ) : ℝ := exp (-x ^ 2) * ∫ t in 0..x, exp (t ^ 2)
/-- **FKS2 remark after Corollary 11**

The Dawson function has a single maximum at $x \approx 0.942$, after which the function is
  decreasing.

PROVIDED SOLUTION:
The Dawson function satisfies the differential equation $F'(x) + 2xF(x) = 1$ from which it follows that the second derivative satisfies $F''(x) = −2F(x) − 2x(−2xF(x) + 1)$, so that at every critical point (where we have $F(x) = \frac{1}{2x}$) we have $F''(x) = −\frac{1}{x}$.  It follows that every positive critical value gives a local maximum, hence there is a unique such critical value and the function decreases after it. Numerically one may verify this is near 0.9241 see https://oeis.org/ A133841.
-/
theorem remark_after_corollary_11 :
    ∃ x₀ : ℝ, x₀ ∈ Set.Icc 0.924 0.925 ∧ (∀ x, dawson x ≤ dawson x₀) ∧
      StrictAntiOn dawson (Set.Ioi x₀) := sorry



/-!
## From asymptotic estimates on psi to asymptotic estimates on theta

To get from asymptotic estimates on $E_\psi$ to asymptotic estimates on $E_\theta$, the paper cites results and arguments from the previous paper [reference], which is treated elsewhere in this blueprint.
-/

noncomputable def ν_asymp (Aψ B C R x₀ : ℝ) : ℝ :=
  (1 / Aψ) * (R / log x₀) ^ B * exp (C * sqrt (log x₀ / R)) *
    (BKLNW.a₁ (log x₀) * (log x₀) * x₀ ^ (-(1:ℝ)/2) +
      BKLNW.a₂ (log x₀) * (log x₀) * x₀ ^ (-(2:ℝ)/3))
/-- **FKS2 Proposition 13**

Suppose that $A_\psi,B,C,R,x_0$ give an admissible bound for $E_\psi$.  If $B > C^2/8R$, then
  $A_\theta, B, C, R, x_0$ give an admissible bound for $E_\theta$, where
  $$ A_\theta = A_\psi (1 + \nu_{asymp}(x_0))$$
  with
  $$ \nu_{asymp}(x_0) = \frac{1}{A_\psi} (\frac{R}{\log x_0})^B
    \exp(C \sqrt{\frac{\log x_0}{R}}) (a_1 (\log x_0) x_0^{-1/2} + a_2 (\log x_0) x_0^{-2/3}).$$
  and $a_1,a_2$ are given by Definitions \ref{bklnw-def-a-1} and \ref{bklnw-def-a-2}.

PROVIDED SOLUTION:
The proof of Corollary \ref{bklnw-cor-14-1} essentially proves the proposition, but requires that $x_0 \geq e^{1000}$ to conclude that the function
  $$ 1 + \frac{a_1 \exp(C \sqrt{\frac{\log x}{R}})}{A_\psi \sqrt{x} (\log x/R)^{B}} + \frac{a_2 \exp(C \sqrt{\frac{\log x}{R}})}{A_\psi x^{2/3} (\log x/R)^{B}} = 1 + \frac{a_1}{A_\psi} g(1/2, -B, C/\sqrt{R}, x) + \frac{a_2}{A_\psi} g(2/3, -B, C/\sqrt{R}, x)$$
  is decreasing. By Lemma \ref{fks2-lemma-10a}, since $B > C^2/8R$, the function is actually decreasing for all $x$.
-/
theorem proposition_13
  (Aψ B C R x₀ : ℝ)
  (h_bound : Eψ.classicalBound Aψ B C R x₀)
  (hB : B > C ^ 2 / (8 * R)) :
  Eθ.classicalBound (Aψ * (1 + ν_asymp Aψ B C R x₀)) B C R x₀ := by sorry


lemma corollary_14_small_adm :
    ∀ {x : ℝ}, 2 ≤ x → x ≤ Real.exp 30 →
    (1:ℝ) ≤ admissible_bound 121.0961 (3/2) 2 5.5666305 x := by
  admit

/-- **FKS2 Corollary 14**

We have an admissible bound for $E_\theta$ with $A = 121.0961$, $B=3/2$, $C=2$,
  $R = 5.5666305$, $x_0=2$.

PROVIDED SOLUTION:
By Corollary \ref{fks_cor_13}, with $R = 5.5666305$, and using the admissible asymptotic bound for $E_\psi(x)$ with $A_\psi = 121.096$, $B = 3/2$, $C = 2$, for all $x \geq x_0 = e^{30}$, we can obtain $\nu_{asymp}(x_0) \leq 6.3376 \cdot 10^{-7}$, from which one can conclude an admissible asymptotic bound for $E_\theta(x)$ with $A_\theta = 121.0961$, $B = 3/2$, $C = 2$, for all $x \geq x_0 = e^{30}$. Additionally, the minimum value of $\varepsilon_{\theta,asymp}(x)$ for $2 \leq x \leq e^{30}$ is roughly $2.6271\ldots$ at $x=2$. The results found in [reference] give $E_\theta(x) \leq 1 < \varepsilon_{\theta,asymp}(2) \leq \varepsilon_{\theta,asymp}(x)$ for all $2 \leq x \leq e^{30}$.
-/
theorem corollary_14 : Eθ.classicalBound 121.0961 (3/2) 2 5.5666305 2 := by
  admit

/-- **FKS2 Remark 15**

If $\log x_0 \geq 1000$ then we have an admissible bound for $E_\theta$ with the indicated
  choice of $A(x_0)$, $B = 3/2$, $C = 2$, and $R = 5.5666305$.

PROVIDED SOLUTION:
From [reference] we have $\nu_{asymp}(x_0) \leq 10^{-200}$. Thus, one easily verifies that the rounding up involved in forming [reference] exceeds the rounding up also needed to apply this step. Consequently we may use values from $A_\theta$ taken from [reference] directly but this does, in contrast to Corollary \ref{fks2-corollary-14}, require the assumption $x > x_0$, as per that table.
-/
theorem remark_15 (x₀ : ℝ) (h : log x₀ ≥ 1000) :
    Eθ.classicalBound (FKS.A x₀) (3/2) 2 5.5666305 x₀ := by sorry


theorem l0 {x y : ℝ} (hx : 2 ≤ x) (hy : x ≤ y) :
    ContinuousOn (fun t ↦ (t * log t ^ 2)⁻¹) (Set.uIcc x y) := by
  admit

theorem Li_identity {x} (hx : 2 ≤ x) :
    Li x = x / log x - 2 / log 2 + ∫ t in 2..x, 1 / (log t ^ 2) := by
  admit

theorem l1 {x y} (hx : 2 ≤ x) (hy : x ≤ y) :
    IntervalIntegrable (fun t ↦ θ t / (t * log t ^ 2)) volume x y := by
  admit

theorem l2 {x y} (hx : 2 ≤ x) (hy : x ≤ y) :
    IntervalIntegrable (fun t ↦ t / (t * log t ^ 2)) volume x y := by
  admit

theorem he {x} (hx : 2 ≤ x) : pi x - Li x = (θ x - x) / log x + 2 / log 2
  + ∫ t in 2..x, (θ t - t) / (t * log t ^ 2) := by
  admit

theorem l3 {x y} (hx : 2 ≤ x) (hy : x ≤ y) :
    IntervalIntegrable (fun t ↦ (θ t - t) / (t * log t ^ 2)) volume x y := by
  admit

/-!
## From asymptotic estimates on theta to asymptotic estimates on pi

To get from asymptotic estimates on $E_\theta$ to asymptotic estimates on $E_\pi$, one first needs a way to express the latter as an integral of the former.
-/
/-- **FKS2 equation (17)**

For any $2 \leq x_0 < x$ one has
  $$ (\pi(x) - \Li(x)) - (\pi(x_0) - \Li(x_0)) = \frac{\theta(x) - x}{\log x}
    - \frac{\theta(x_0) - x_0}{\log x_0} + \int_{x_0}^x \frac{\theta(t) - t}{t \log^2 t} dt.$$

PROVIDED SOLUTION:
This follows from Sublemma \ref{rs-417}.
-/
theorem eq_17 {x₀ x : ℝ} (hx₀ : 2 ≤ x₀) (hx : x₀ < x) :
    (pi x - Li x) - (pi x₀ - Li x₀) =
    (θ x - x) / log x - (θ x₀ - x₀) / log x₀ +
    ∫ t in x₀..x, (θ t - t) / (t * log t ^ 2) := by
  admit

/-!
The following definition is only implicitly in FKS2, but will be convenient:
-/
/-- **Defining an error term**

For any $x_0>0$, we define
  $$\delta(x_0) := |\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}|.$$
-/
noncomputable def δ (x₀ : ℝ) : ℝ :=
  |(pi x₀ - Li x₀) / (x₀ / log x₀) - (θ x₀ - x₀) / x₀|

/-!
We can now obtain an upper bound on $E_\pi$ in terms of $E_\theta$:
-/
/-- **FKS2 Equation (30)**

For any $x \geq x_0 > 0$,
  $$ |\pi(x) - \Li(x)| \leq \left| \frac{\theta(x) - x}{\log(x)} \right| + \left| \pi(x_0) - \Li(x_0) - \frac{\theta(x_0) - x_0}{\log(x_0)} \right| + \left| \int_{x_0}^{x} \frac{\theta(t) - t}{t(\log(t))^2} \, dt \right|. $$

PROVIDED SOLUTION:
This follows from applying the triangle inequality to Sublemma \ref{fks2-eq-17}.
-/
theorem eq_30 {x x₀ : ℝ} (hx : x ≥ x₀) (hx₀ : x₀ ≥ 2) :
  Eπ x ≤ Eθ x + (log x / x) * (x₀ / log x₀) * δ x₀ + (log x / x) * ∫ t in x₀..x, Eθ t / log t ^ 2 := by
  admit

/-!
Next, we bound the integral appearing in Sublemma \ref{fks2-eq-17}.
-/
/-- **FKS2 Lemma 12**

Suppose that $E_\theta$ satisfies an admissible classical bound with parameters $A,B,C,R,x_0$.
  Then, for all $x \geq x_0$,
  $$ \int_{x_0}^x \left|\frac{E_\theta(t)}{\log^2 t} dt\right| \leq \frac{2A}{R^B} x m(x_0,x)
    \exp\left(-C \sqrt{\frac{\log x}{R}}\right) D_+\left( \sqrt{\log x} - \frac{C}{2\sqrt{R}} \right)$$
  where
  $$ m(x_0,x) = \max ( (\log x_0)^{(2B-3)/2}, (\log x)^{(2B-3)/2} ). $$

PROVIDED SOLUTION:
Since $\varepsilon_{\theta,\mathrm{asymp}}(t)$ provides an admissible bound on $\theta(t)$ for all $t \geq x_0$, we have
$$
\int_{x_0}^{x} \left| \frac{\theta(t) - t}{t(\log(t))^2} \right| dt \leq \int_{x_0}^{x} \frac{\varepsilon_{\theta,\mathrm{asymp}}(t)}{(\log(t))^2} = \frac{A_\theta}{R^B} \int_{x_0}^{x} (\log(t))^{B-2} \exp\left( -C\sqrt{\frac{\log(t)}{R}} \right) dt.
$$
We perform the substitution $u = \sqrt{\log(t)}$ and note that $u^{2B-3} \leq m(x_0, x)$ as defined in (21). Thus the above is bounded above by
$$
\frac{2A_\theta m(x_0, x)}{R^B} \int_{\sqrt{\log(x_0)}}^{\sqrt{\log(x)}} \exp\left( u^2 - \frac{Cu}{\sqrt{R}} \right) du.
$$
Then, by completing the square $u^2 - \frac{Cu}{\sqrt{R}} = \left( u - \frac{C}{2\sqrt{R}} \right)^2 - \frac{C^2}{4R}$ and doing the substitution $v = u - \frac{C}{2\sqrt{R}}$, the above becomes
$$
\frac{2A_\theta m(x_0, x)}{R^B} \exp\left( -\frac{C^2}{4R} \right) \int_{\sqrt{\log(x_0)} - \frac{C}{2\sqrt{R}}}^{\sqrt{\log(x)} - \frac{C}{2\sqrt{R}}} \exp(v^2) \, dv.
$$
Now we have
\begin{align*}
\int_{\sqrt{\log(x_0)} - \frac{C}{2\sqrt{R}}}^{\sqrt{\log(x)} - \frac{C}{2\sqrt{R}}} \exp(v^2) \, dv &\leq \int_{0}^{\sqrt{\log(x)} - \frac{C}{2\sqrt{R}}} \exp(v^2) \, dv \\
&= x \exp\left( \frac{C^2}{4R} \right) \exp\left( -C\sqrt{\frac{\log(x)}{R}} \right) D_+\left( \sqrt{\log(x)} - \frac{C}{2\sqrt{R}} \right).
\end{align*}
Combining the above completes the proof.
-/
theorem lemma_12 {A B C R x₀ x : ℝ} (hEθ : Eθ.classicalBound A B C R x₀) (hx : x ≥ x₀)
    (hx₀ : 2 ≤ x₀) (hR : 0 < R) (hA : 0 ≤ A) (h : 0 ≤ √(log x₀) - C / (2 * √R)) :
  ∫ t in x₀..x, |Eθ t| / log t ^ 2 ≤
    (2 * A) / (R ^ B) * x * max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2)) *
    exp (-C * sqrt (log x / R)) * dawson (sqrt (log x) - C / (2 * sqrt R)) := by
  admit

/-- **mu asymptotic function, FKS2 (9)**

For $x_0,x_1 > 0$, we define
  $$ \mu_{asymp}(x_0,x_1) := \frac{x_0 \log(x_1)}{\epsilon_{\theta,asymp}(x_1) x_1 \log(x_0)}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right| +
    \frac{2D_+(\sqrt{\log(x_1)} - \frac{C}{2\sqrt{R}}}{\sqrt{\log x_1}}$$.
-/
noncomputable def μ_asymp (A B C R x₀ x₁ : ℝ) : ℝ :=
  (x₀ * log x₁) / ((admissible_bound A B C R x₁) * x₁ * log x₀) * δ x₀ +
    2 * (dawson (sqrt (log x₁) - C / (2 * sqrt R))) / (sqrt (log x₁))

/-!
We obtain our final bound for converting bounds on $E_\theta$ to bounds on $E_\pi$.
-/
/-- **FKS2 Theorem 3**

If $B \geq \max(3/2, 1 + C^2/16 R)$, $x_0 > 0$, and one has an admissible asymptotic bound
  with parameters $A,B,C,x_0$ for $E_\theta$, and
  $$ x_1 \geq \max( x_0, \exp( (1 + \frac{C}{2\sqrt{R}}))^2),$$
  then
  $$ E_\pi(x) \leq \epsilon_{\theta,asymp}(x_1) ( 1 + \mu_{asymp}(x_0,x_1) ) $$
  for all $x \geq x_1$.  In other words, we have an admissible bound with parameters
  $(1+\mu_{asymp}(x_0,x_1))A, B, C, x_1$ for $E_\pi$.

PROVIDED SOLUTION:
The starting point is Sublemma \ref{fks2-eq30}.
  The assumption ($\varepsilon_{\theta,\mathrm{asymp}}(x)$ provides an admissible bound on $\theta(x)$ for all $x \geq x_0$) to bound $\frac{\theta(x) - x}{\log(x)}$ and Lemma \ref{fks2-lemma-12} to bound $\int_{x_0}^{x} \frac{\theta(t) - t}{t (\log(t))^2} dt$.  We obtain
  $$ |\pi(x) - \Li(x)| \leq |\pi(x_0) - \Li(x_0) - \frac{\theta(x_0) - x_0}{\log(x_0)}| + \frac{x \varepsilon_{\theta,\mathrm{asymp}}(x)}{\log(x)} + \frac{2 A_\theta}{R^B} x m(x_0,x) \exp(-C \sqrt{\frac{\log x}{R}}) D_+\left( \sqrt{\log x} - \frac{C}{2\sqrt{R}} \right).$$
  We recall that $x \geq x_1 \geq x_0$.  Note that, by Corollary \ref{fks2-corollary-11},
  $$ \frac{\log(x)}{x \varepsilon_{\theta,\mathrm{asymp}}(x)} = \frac{1}{A_\theta} g(1, 1 - B, \frac{C}{\sqrt{R}}, x) $$
  is decreasing for all $x$.  Thus,
  $$ \frac{\log(x)}{x \varepsilon_{\theta,\mathrm{asymp}}(x)} \leq \frac{\log(x_1)}{x_1 \varepsilon_{\theta,\mathrm{asymp}}(x_1)}. $$
  In addition, we have the simplification
  $$ \frac{\log(x)}{x \varepsilon_{\theta,\mathrm{asymp}}(x)} \frac{2 A_\theta}{R^B} x m(x_0,x) e^{-C \sqrt{\frac{\log x}{R}}} = 2 m(x_0,x) (\log(x))^{1 - B} = 2 (\log(x))^{1 - B} \leq 2 (\log(x_1))^{1 - B}, $$
  by Definition \ref{classical-bound-theta} and by $m(x_0,x) = (\log(x))^{(2B - 3)/2}$, since $B \geq 3/2$.  Finally, since $\sqrt{\log(x_1)} - \frac{C}{2\sqrt{R}} > 1$, the Dawson function decreases for all $x \geq x_1$:
  $$ D_+\left( \sqrt{\log x} - \frac{C}{2\sqrt{R}} \right) \leq D_+\left( \sqrt{\log x_1} - \frac{C}{2\sqrt{R}} \right). $$
  We conclude by combining the above:
  $$ \frac{|\pi(x) - \Li(x)|}{\frac{x \varepsilon_{\theta,\mathrm{asymp}}(x)}{\log(x)}} \leq \frac{\log(x_1)}{x_1 \varepsilon_{\theta,\mathrm{asymp}}(x_1)} |\pi(x_0) - \Li(x_0) - \frac{\theta(x_0) - x_0}{\log(x_0)}| + 1 + \frac{2 D_+\left( \sqrt{\log x_1} - \frac{C}{2\sqrt{R}} \right)}{\sqrt{\log(x_1)}}, $$
  from which we deduce the announced bound.
-/
theorem theorem_3 (A B C R x₀ x₁ : ℝ)
  (hB : B ≥ max (3 / 2) (1 + C ^ 2 / (16 * R)))
  (hx0 : x₀ > 0)
  (hE_theta : Eθ.classicalBound A B C R x₀)
  (hx1 : x₁ ≥ max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2))) :
  Eπ.classicalBound (A * (1 + μ_asymp A B C R x₀ x₁)) B C R x₁ :=
  sorry



/-!
## From numerical estimates on psi to numerical estimates on theta

Here we record a way to convert a numerical bound on $E_\psi$ to a numerical bound on $E_\theta$.
-/

noncomputable def εθ_from_εψ (εψ : ℝ → ℝ) (x₀ : ℝ) : ℝ :=
  εψ x₀ + 1.00000002 * (x₀ ^ (-(1:ℝ)/2) + x₀ ^ (-(2:ℝ)/3) + x₀ ^ (-(4:ℝ)/5)) +
    0.94 * (x₀ ^ (-(3:ℝ)/4) + x₀ ^ (-(5:ℝ)/6) + x₀ ^ (-(9:ℝ)/10))

/-- Bound for `ψ(y)` for small `y`. -/
theorem psi_le_bound_small (y : ℝ) (hy1 : 1 < y) (hy2 : y < 100) :
    ψ y ≤ 1.00000002 * y + 0.94 * y ^ (1/2 : ℝ) := by
  admit

/-- Bound for `ψ(y)` for medium `y`. -/
theorem psi_le_bound_medium (y : ℝ) (hy1 : 100 ≤ y) (hy2 : y ≤ 1e19) :
    ψ y ≤ 1.00000002 * y + 0.94 * y ^ (1/2 : ℝ) := by
  admit

/-- Bound for `ψ(y)` for large `y`. -/
theorem psi_le_bound_large (y : ℝ) (hy : 1e19 < y) :
    ψ y ≤ 1.00000002 * y + 0.94 * y ^ (1/2 : ℝ) := by
  admit

/-- Bound for `ψ(y)` for all `y > 1`. -/
theorem psi_le_bound (y : ℝ) (hy : 1 < y) : ψ y ≤ 1.00000002 * y + 0.94 * y ^ (1/2 : ℝ) := by
  admit

/-- **FKS2 Proposition 17**

Let $x > x_0 > 2$.  If $E_\psi(x) \leq \varepsilon_{\psi,num}(x_0)$, then
  $$ - \varepsilon_{\theta,num}(x_0) \leq \frac{\theta(x)-x}{x}
    \leq \varepsilon_{\psi,num}(x_0) \leq \varepsilon_{\theta,num}(x_0)$$
  where
  $$ \varepsilon_{\theta,num}(x_0) = \varepsilon_{\psi,num}(x_0) +
    1.00000002(x_0^{-1/2}+x_0^{-2/3}+x_0^{-4/5}) +
    0.94 (x_0^{-3/4} + x_0^{-5/6} + x_0^{-9/10})$$

PROVIDED SOLUTION:
The upper bound is immediate since $\theta(x) \leq \psi(x)$ for all $x$. For the lower bound, we have
  $$\frac{\theta(x) - x}{x} = \frac{\psi(x) - x}{x} + \frac{\theta(x) - \psi(x)}{x}.$$
  By Theorem \ref{costa-pereira-theorem-1a}, we have
  $$\psi(x) - \theta(x) \leq \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}).$$
  We use [reference], that for $0 < x < 11$, $\psi(x) < x$, and that $\varepsilon_{\psi,num}(10^{19}) < 2 \cdot 10^{-8}$. In particular when $2 < x < 10^{38}$,
  $$\psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) \leq x^{1/2} + x^{1/3} + x^{1/5} + 0.94(x^{1/4} + x^{1/6} + x^{1/10}),$$
  when $10^{38} \leq x < 10^{54}$,
  $$\psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) \leq 1.00000002x^{1/2} + x^{1/3} + x^{1/5} + 0.94(x^{1/6} + x^{1/10}),$$
  when $10^{54} \leq x < 10^{95}$,
  $$\psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) \leq 1.00000002(x^{1/2} + x^{1/3}) + x^{1/5} + 0.94x^{1/10},$$
  and finally when $x \geq 10^{95}$,
  $$\psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) \leq 1.00000002(x^{1/2} + x^{1/3} + x^{1/5}).$$
  The result follows by combining the worst coefficients from all cases and dividing by $x$.
-/
theorem proposition_17 {x x₀ : ℝ} (hx : x > x₀) (hx₀ : x₀ > 2) (εψ : ℝ → ℝ) (hEψ : Eψ x ≤ εψ x₀) :
    -εθ_from_εψ εψ x₀ ≤ (θ x - x) / x ∧ (θ x - x) / x ≤ εψ x₀ ∧ εψ x₀ ≤ εθ_from_εψ εψ x₀ := by
  admit

/-!
## From numerical estimates on theta to numerical estimates on pi

Here we record a way to convert a numerical bound on $E_\theta$ to a numerical bound on $E_\pi$.  We first need some preliminary lemmas.
-/

theorem Li_identity' {a b : ℝ} (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in a..b, 1 / log t ^ 2 = Li b - Li a - b / log b + a / log a := by
  admit

/-- **FKS2 Lemma 19**

Let $x_1 > x_0 \geq 2$, $N \in \N$, and let $(b_i)_{i=1}^N$ be a finite partition of
  $[\log x_0, \log x_1]$.  Then
  $$ |\int_{x_0}^{x_1} \frac{\theta(t)-t}{t \log^2 t}\ dt|
    \leq \sum_{i=1}^{N-1} \eps_{\theta,num}(e^{b_i})
    ( \Li(e^{b_{i+1}}) - \Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}}).$$

PROVIDED SOLUTION:
We split the integral at each $e^{b_i}$ and apply the bound
  $$ |\frac{\theta(t)-t}{t}| \leq \eps_{\theta,num}(e^{b_i}), \text{ for every } e^{b_i} \leq t < e^{b_{i+1}}. $$
  Thus,
  $$ |\int_{x_0}^{x_1} \frac{\theta(t)-t}{t \log^2 t}\ dt|
    \leq \sum_{i=1}^{N-1} \int_{e^{b_i}}^{e^{b_{i+1}}}
      |\frac{\theta(t)-t}{t \log^2 t}|\ dt
    \leq \sum_{i=1}^{N-1} \eps_{\theta,num}(e^{b_i})
      \int_{e^{b_i}}^{e^{b_{i+1}}} \frac{dt}{(\log t)^2}. $$
  We conclude by using the identity: for all $2 \leq a < b$,
  $$ \int_a^b \frac{dt}{(\log t)^2}
    = \Li(b) - \frac{b}{\log b} - (\Li(a) - \frac{a}{\log a}). $$
-/
theorem lemma_19 {x₀ x₁ : ℝ} (hx₁ : x₀ < x₁) (hx₀ : x₀ ≥ 2)
  {N : ℕ} (b : ℕ → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀) (hN : 0 ≤ N)
  (h_b_end : b N = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : ∀ i ∈ Finset.Ico 0 N, Eθ.numericalBound (exp (b i)) εθ_num) :
  |∫ t in x₀..x₁, (θ t - t) / (t * log t ^ 2)| ≤
    ∑ i ∈ Finset.Ico 0 N,
      εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1)) := by
  admit

lemma hasDerivAt_Li {x : ℝ} (hx : x ∈ Set.Ioi 6.58) : HasDerivAt Li (1 / log x) x := by
  admit

/-- **FKS2 Lemma 20a**

The function $\Li(x) - \frac{x}{\log x}$ is strictly increasing for $x > 6.58$.

PROVIDED SOLUTION:
Differentiate
  $$
  \frac{d}{dx} \left( \Li(x) - \frac{x}{\log(x)} \right) = \frac{1}{\log(x)} + \frac{1 - \log(x)}{(\log(x))^2} = \frac{1}{(\log(x))^2}
  $$
  to see that the difference is strictly increasing. Evaluating at $x = 6.58$ and applying the mean value theorem gives the announced result.
-/
theorem lemma_20_a : StrictMonoOn (fun x ↦ Li x - x / log x) (Set.Ioi 6.58) := by
  admit

/- [FIX]: This fixes a typo in the original paper https://arxiv.org/pdf/2206.12557. -/
/-- **FKS2 Lemma 20b**

Assume $x > 6.58$. Then
  $\Li(x) - \frac{x}{\log x} > \frac{x-6.58}{\log^2 x} > 0$.

PROVIDED SOLUTION:
This follows from Lemma \ref{fks2-lemma-20a} and the mean value theorem.
-/
theorem lemma_20_b {x : ℝ} (hx : x > 6.58) :
    Li x - x / log x > (x - 6.58) / (log x) ^ 2 ∧ (x - 6.58) / (log x) ^ 2 > 0 :=
  sorry


/-!
Now we can start estimating $E_\pi$.  We make the following running hypotheses. Let $x_0 > 0$ be chosen such that $\pi(x_0)$ and $\theta(x_0)$ are computable, and let   $x_1 \geq \max(x_0, 14)$. Let $\{b_i\}_{i=1}^N$ be a finite partition of   $[\log x_0, \log x_1]$, with $b_1 = \log x_0$ and $b_N = \log x_1$, and suppose that   $\varepsilon_{\theta,\mathrm{num}}$ gives numerical bounds for $x = \exp(b_i)$, for each $i=1,\dots,N$.
-/
/-- **FKS2 Theorem 6, substep 1**

With the above hypotheses, for all $x \geq x_1$ we have
  $$ E_\pi(x) \leq \varepsilon_{θ,num}(x_1) + \frac{\log x}{x} \frac{x_0}{\log x_0} (E_\pi(x_0) + E_\theta(x_0))$$
  $$ + \frac{\log x}{x} \sum_{i=1}^{N-1} \varepsilon_{\theta,num}(e^{b_i}) \left( \Li(e^{b_{i+1}}) - \Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}} \right) $$
  $$ + \varepsilon_{\theta,num}(x_1) \frac{\log x}{x} \int_{x_1}^{x} \frac{1}{(\log t)^2} \, dt. $$

PROVIDED SOLUTION:
This is obtained by combining Sublemma \ref{fks2-eq-30} with the admissibility of $\varepsilon_{\theta,num}$ and Lemma \ref{fks2-lemma-19}.
-/
theorem theorem_6_1 {x₀ x₁ : ℝ} (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx : x ≥ x₁) :
  Eπ x ≤ εθ_num x₁ + (log x / x) * (x₀ / log x₀) * (Eπ x₀ + Eθ x₀) +
    (log x / x) * ∑ i ∈ Finset.Iio (Fin.last N),
      εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1)) +
    εθ_num x₁ * (log x / x) * ∫ t in x₁..x, 1 / (log t) ^ 2 :=
  sorry

/-- **FKS2 Theorem 6, substep 2**

With the above hypotheses, for all $x \geq x_1$ we have
  $$ \frac{\log x}{x} \int_{x_1}^x \frac{dt}{\log^2 t} < \frac{1}{\log x_1 + \log \log x_1 - 1}. $$

PROVIDED SOLUTION:
Call the left-hand side $f(x)$. We have
  $$ f(x) = \frac{\log x}{x} \left( \mathrm{Li}(x) - \frac{x}{\log x} - \mathrm{Li}(x_1) + \frac{x_1}{\log x_1} \right). $$
  Using integration by parts, its derivative can be written as
  $$ f'(x) = -\frac{1}{x \log^2 x} + \frac{2}{x \log^3 x} + \frac{\log x - 1}{x^2} \left( \frac{x_1}{\log^2 x_1} + \frac{2 x_1}{\log^3 x_1} - \int_{x_1}^x \frac{6}{\log^4 t} dt \right). $$
  From which we see that $f'(x_1) = \frac{1}{\log x_1} > 0$, and that $f'(x)$ is eventually negative. Thus there exists a critical point for $f(x)$ to the right of $x_1$. Moreover, by bounding $\int_{x_1}^x \frac{6}{\log^4 t} dt < 6 \frac{x - x_1}{\log^4 x_1}$, one finds that $f'(x_1 \log x_1) > 0$ if $x_1 > e$.
  Now we write $f'(x) = \frac{f_1(x)}{x^2}$ with
  $$ f_1(x) = \frac{x}{\log x} - (\log x - 1) \int_{x_1}^x \frac{1}{\log^2 t} dt. $$
  Its derivative is $f_1'(x) = -\frac{1}{x} \int_{x_1}^x \frac{1}{\log^2 t} dt$, which is negative for $x > x_1$. Thus $f_1(x)$ decreases and vanishes at most once, giving $f(x)$ at most one critical point, $x_m > x_1$, which is then the maximum of $f(x)$. In other words, $x_m$ satisfies $f_1(x_m) = 0$, i.e.\ $\mathrm{Li}(x_m) - \mathrm{Li}(x_1) + \frac{x_1}{\log x_1} = -\frac{x_m}{1 - \log x_m}$, which shows that $f(x)$ attains its maximum at $x = x_m$, where
  $$ f(x_m) = \frac{\log x_m}{x_m} \left( -\frac{x_m}{\log x_m} - \frac{x_m}{1 - \log x_m} \right) = \frac{1}{\log x_m - 1}. $$
  Now, because $x_m > x_1 \log x_1$ we obtain the bound
  $$ f(x) < \frac{1}{\log x_1 + \log(\log x_1) - 1}, $$
  which gives the announced result.
-/
theorem theorem_6_2 {x₁ : ℝ} (h : x₁ ≥ 14) (x : ℝ) (hx : x ≥ x₁) :
  (log x / x) * ∫ t in x₁..x, 1 / (log t) ^ 2 < 1 / (log x₁ + log (log x₁) - 1) :=
  sorry

/-- **FKS2 Theorem 6, substep 3**

With the above hypotheses, for all $x \geq x_1$ we have
  $$ \frac{\log x}{x} \int_{x_1}^x \frac{dt}{\log^2 t} \leq \frac{\log x_2}{x_2} \left( \Li(x_2) - \frac{x_2}{\log x_2} - \Li(x_1) + \frac{x_1}{\log x_1} \right ). $$

PROVIDED SOLUTION:
Let $f(x)$ be as in the previous sublemma.  Notice that by assumption $x_1 \leq x \leq x_2 \leq x_1 \log x_1 < x_m$, so that
  $$ f(x) \leq f(x_2) = \frac{\log x_2}{x_2} \left( \Li(x_2) - \frac{x_2}{\log x_2} - \Li(x_1) + \frac{x_1}{\log x_1} \right). $$
-/
theorem theorem_6_3 {x₁ : ℝ} (h : x₁ ≥ 14) (x₂ : ℝ) (hx₂ : x₂ ≥ x₁) (x : ℝ) (hx : x ≥ x₁) (hx' : x ≤ x₂) :
  (log x / x) * ∫ t in x₁..x, 1 / (log t) ^ 2 ≤
    (log x₂ / x₂) * (Li x₂ - x₂ / log x₂ - Li x₁ + x₁ / log x₁) :=
  sorry


/-!
We can merge these sublemmas together after making some definitions.
-/
/-- **FKS2 equation (11)**

For $x_1 \leq x_2 \leq x_1 \log x_1$, we define
  $$ \mu_{num,1}(x_0,x_1,x_2) := \frac{x_0 \log(x_1)}{\epsilon_{\theta,num}(x_1) x_1 \log(x_0)}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right| +
    \frac{\log(x_1)}{\epsilon_{\theta,num}(x_1) x_1}
    \sum_{i=0}^{N-1} \epsilon_{\theta,num}(e^{b_i})
    \left( \Li(e^{b_{i+1}}) - \Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}} \right) +
    \frac{\log(x_2)}{x_2} \left( \Li(x_2) - \frac{x_2}{\log x_2} - \Li(x_1) + \frac{x_1}{\log x_1} \right).$$
-/
noncomputable def μ_num_1 {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) : ℝ :=
  (x₀ * log x₁) / (εθ_num x₁ * x₁ * log x₀) * δ x₀ +
  (log x₁) / (εθ_num x₁ * x₁) *
    (∑ i ∈ Finset.Iio (Fin.last N), εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1))) +
    (log x₂) / x₂ * (Li x₂ - x₂ / log x₂ - Li x₁ + x₁ / log x₁)
/-- **FKS2 equation (12)**

For $x_2 \geq x_1 \log x_1$, we define
  $$ \mu_{num,2}(x_0,x_1) := \frac{x_0 \log(x_1)}{\epsilon_{\theta,num}(x_1) x_1 \log(x_0)}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right| +
    \frac{\log(x_1)}{\epsilon_{\theta,num}(x_1) x_1}
    \sum_{i=0}^{N-1} \epsilon_{\theta,num}(e^{b_i})
    \left( \Li(e^{b_{i+1}}) - \Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}} \right) +
    \frac{1}{\log x_1 + \log(\log x_1) - 1}.$$
-/
noncomputable def μ_num_2 {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ) : ℝ :=
  (x₀ * log x₁) / (εθ_num x₁ * x₁ * log x₀) * δ x₀ +
  (log x₁) / (εθ_num x₁ * x₁) *
    (∑ i ∈ Finset.Iio (Fin.last N), εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1))) +
    1 / (log x₁ + log (log x₁) - 1)
/-- **Definition of mu**

We define $\mu_{num}(x_0, x_1, x_2)$ to equal $\mu_{num,1}(x_0,x_1,x_2)$ when $x_2 \leq x_1 \log x_1$ and $\mu_{num,2}(x_0,x_1)$ otherwise.
-/
noncomputable def μ_num {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ) (x₂ : EReal) : ℝ :=
  if x₂ ≤ x₁ * log x₁ then
    μ_num_1 b εθ_num x₀ x₁ x₂.toReal
  else
    μ_num_2 b εθ_num x₀ x₁
/-- **FKS2 equation (13)**

For $x_1 \leq x_2$, we define $\epsilon_{\pi,num}(x_0,x_1,x_2) := \epsilon_{\theta,num}(x_1)
    (1 + \mu_{num}(x_0,x_1,x_2))$.
-/
noncomputable def επ_num {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ)
    (x₂ : EReal) : ℝ :=
  εθ_num x₁ * (1 + μ_num b εθ_num x₀ x₁ x₂)

noncomputable def default_b (x₀ x₁ : ℝ) : Fin 2 → ℝ :=
  fun i ↦ if i = 0 then log x₀ else log x₁

/- [NOTE]: The original FKS2 paper states the derivative condition
`deriv (fun x ↦ (log x) / x * (Li x - x / log x - Li x₁ + x₁ / log x₁)) x₂ ≥ 0`
as a hypothesis for this remark. However, Aristotle's proof shows it is not required. -/
/-- **FKS2 Remark 7**

If
  $$ \frac{d}{dx} \frac{\log x}{x}
    \left( \Li(x) - \frac{x}{\log x} - \Li(x_1) + \frac{x_1}{\log x_1} \right)|_{x_2} \geq 0 $$
  then $\mu_{num,1}(x_0,x_1,x_2) < \mu_{num,2}(x_0,x_1)$.

PROVIDED SOLUTION:
This follows from the definitions of $\mu_{num,1}$ and $\mu_{num,2}$.
-/
theorem remark_7 {x₀ x₁ : ℝ} (x₂ : ℝ) (h : x₁ ≥ max x₀ 14)
    {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x : ℝ) (hx₁ : x₁ ≤ x) (hx₂ : x ≤ x₂) :
    μ_num_1 b εθ_num x₀ x₁ x₂ < μ_num_2 b εθ_num x₀ x₁ := by
  admit

/-!
This gives us the final result to obtain numerical bounds for $E_\pi$ from numerical bounds on $E_\theta$.
-/
/-- **FKS2 Theorem 6**
-/
theorem theorem_6 {x₀ x₁ : ℝ} (x₂ : EReal) (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx₁ : x₁ ≤ x) (hx₂ : x.toEReal ≤ x₂) :
  Eπ x ≤ επ_num b εθ_num x₀ x₁ x₂ :=
  sorry

/-- **FKS2 Theorem 6**

Let $x_0 > 0$ be chosen such that $\pi(x_0)$ and $\theta(x_0)$ are computable, and let
  $x_1 \geq \max(x_0, 14)$. Let $\{b_i\}_{i=1}^N$ be a finite partition of
  $[\log x_0, \log x_1]$, with $b_1 = \log x_0$ and $b_N = \log x_1$, and suppose that
  $\varepsilon_{\theta,\mathrm{num}}$ gives computable admissible numerical bounds for
  $x = \exp(b_i)$, for each $i=1,\dots,N$.  For $x_1 \leq x_2 \leq x_1 \log x_1$, we define
  $$ \mu_{num}(x_0,x_1,x_2) = \frac{x_0 \log x_1}{\varepsilon_{\theta,num}(x_0) x_1 \log x_0}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right|$$
  $$ + \frac{\log x_1}{\varepsilon_{\theta,num}(x_1) x_1} \sum_{i=1}^{N-1}
    \varepsilon_{\theta,num}(\exp(b_i))
    \left( \Li(e^{b_{i+1}}) - \Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}}\right)$$
  $$ + \frac{\log x_2}{x_2}
    \left( \Li(x_2) - \frac{x_2}{\log x_2} - \Li(x_1) + \frac{x_1}{\log x_1} \right)$$
  and for $x_2 > x_1 \log x_1$, including the case $x_2 = \infty$, we define
  $$ \mu_{num}(x_0,x_1,x_2) = \frac{x_0 \log x_1}{\varepsilon_{\theta,num}(x_1) x_1 \log x_0}
    \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right|$$
  $$ + \frac{\log x_1}{\varepsilon_{\theta,num}(x_1) x_1} \sum_{i=1}^{N-1}
    \varepsilon_{\theta,num}(\exp(b_i))
    \left( \Li(e^{b_{i+1}}) - \Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}}\right)$$
  $$ + \frac{1}{\log x_1 + \log\log x_1 - 1}.$$
  Then, for all $x_1 \leq x \leq x_2$ we have
  $$ E_\pi(x) \leq \varepsilon_{\pi,num}(x_1,x_2) :=
    \varepsilon_{\theta,num}(x_1)(1 + \mu_{num}(x_0,x_1,x_2)).$$

PROVIDED SOLUTION:
This follows by combining the three substeps.
-/
theorem theorem_6_alt {x₀ x₁ : ℝ} (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx₁ : x₁ ≤ x) :
  Eπ x ≤ εθ_num x₁ * (1 + μ_num_2 b εθ_num x₀ x₁) :=
  sorry

/-- **FKS2 Corollary 8**

Let $\{b'_i\}_{i=1}^M$ be a set of finite subdivisions of $[\log(x_1),\infty)$, with
  $b'_1 = \log(x_1)$ and $b'_M = \infty$. Define
  $$ \varepsilon_{\pi, num}(x_1) :=
    \max_{1 \leq i \leq M-1}\varepsilon_{\pi, num}(\exp(b'_i),
    \exp(b'_{i+1})).$$
  Then $E_\pi(x) \leq \varepsilon_{\pi,num}(x_1)$ for all $x \geq x_1$.

PROVIDED SOLUTION:
This follows directly from Theorem \ref{fks2-theorem-6} by taking the supremum over all partitions ending at infinity.
-/
theorem corollary_8 {x₁ : ℝ} (hx₁ : x₁ ≥ 14)
    {M : ℕ} (b' : Fin (M + 1) → EReal) (hmono : Monotone b')
    (h_b_start : b' 0 = log x₁)
    (h_b_end : b' (Fin.last M) = ⊤)
    (εθ_num : ℝ → ℝ)
    (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx : x ≥ x₁) :
    Eπ x ≤ iSup (fun i : Finset.Iio (Fin.last M) ↦
      επ_num (fun j : Fin (i.val.val+1) ↦ (b' ⟨ j.val, by grind ⟩).toReal)
        εθ_num x₁ (exp (b' i.val).toReal)
        (if (i+1) = Fin.last M then ⊤ else exp (b' (i+1)).toReal)) :=
  sorry


/-!
## Putting everything together

By merging together the above tools with various parameter choices, we can obtain some clean corollaries.
-/
/-- **FKS2 Corollary 21**

Let $B \geq \max(\frac{3}{2}, 1 + \frac{C^2}{16R})$ and $B > C^2/8R$.  Let $x_0, x_1 > 0$ with
  $x_1 \geq \max(x_0, \exp( (1 + \frac{C}{2\sqrt{R}})^2))$. If $E_\psi$ satisfies an admissible
  classical bound with parameters $A_\psi,B,C,R,x_0$, then $E_\pi$ satisfies an admissible
  classical bound with $A_\pi, B, C, R, x_1$, where
  $$ A_\pi = (1 + \nu_{asymp}(x_0)) (1 + \mu_{asymp}(x_0, x_1)) A_\psi$$
  for all $x \geq x_0$, where
  $$ |E_\theta(x)| \leq \varepsilon_{\theta,asymp}(x) :=
    A (1 + \mu_{asymp}(x_0,x)) \exp(-C \sqrt{\frac{\log x}{R}})$$
  where
  $$ \nu_{asymp}(x_0) = \frac{1}{A_\psi} (\frac{R}{\log x_0})^B
    \exp(C \sqrt{\frac{\log x_0}{R}}) (a_1 (\log x_0) x_0^{-1/2} + a_2 (\log x_0) x_0^{-2/3})$$
  and
  $$ \mu_{asymp}(x_0,x_1) = \frac{x_0 \log x_1}{\eps_{\theta,asymp}(x_1)x_1 \log x_0}
    |E_\pi(x_0) - E_\theta(x_0)| + \frac{2 D_+(\sqrt{\log x} - \frac{C}{2\sqrt{R}})}
    {\sqrt{\log x_1}}.$$

PROVIDED SOLUTION:
This follows by applying Theorem \ref{fks2-theorem-3} with Proposition \ref{fks2-proposition-13}.  The hypothesis $B > C^2/8R$ is not present in original source.
-/
theorem corollary_21
  (Aψ B C R x₀ x₁ : ℝ)
  (hB : B ≥ max (3 / 2) (1 + C ^ 2 / (16 * R)))
  (hB' : B > C ^ 2 / (8 * R))
  (hx0 : x₀ > 0)
  (hx1 : x₁ ≥ max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2)))
  (hEψ : Eψ.classicalBound Aψ B C R x₀) :
  let Aθ := Aψ * (1 + ν_asymp Aψ B C R x₀)
  Eπ.classicalBound (Aθ * (1 + (μ_asymp Aθ B C R x₀ x₁))) B C R x₁ := by
  admit

/-- Values for $\eps_{\pi, num}(x_1) are calculated using Corollary 8 with Theorem 6. Note that here $x_0=1015$ and that our sets $\{b_i\}_{i=1}^N$ and $\{b'_i\}_{i=1}^M$ are more refined than as provided by Tables 1, 2, and 3. -/
def Table_4 : List (ℝ × ℝ) := [
  (44, 1.7893e-8), (45, 1.1449e-8), (46, 7.2959e-9), (47, 4.6388e-9), (48, 2.9451e-9),
  (49, 1.8680e-9), (50, 1.1785e-9), (51, 7.4479e-10), (52, 4.7046e-10), (53, 2.9707e-10),
  (54, 1.8753e-10), (55, 1.1785e-10), (56, 7.4191e-11), (57, 4.6692e-11), (58, 2.9380e-11),
  (59, 1.8774e-11), (60, 1.2330e-11), (61, 8.4134e-12), (62, 6.0325e-12), (63, 4.5827e-12),
  (64, 3.6978e-12), (65, 3.1557e-12), (66, 2.8216e-12), (67, 2.6138e-12), (68, 2.4828e-12),
  (69, 2.3985e-12), (70, 2.3427e-12), (71, 2.3043e-12), (72, 2.2766e-12), (73, 2.2555e-12),
  (74, 2.2387e-12), (75, 2.2244e-12), (76, 2.2120e-12), (77, 2.2006e-12), (78, 2.1901e-12),
  (79, 2.1802e-12), (80, 2.1708e-12), (81, 2.1617e-12), (82, 2.1530e-12), (83, 2.1446e-12),
  (84, 2.1364e-12), (85, 2.1284e-12), (86, 2.1207e-12), (87, 2.1132e-12), (88, 2.1059e-12),
  (89, 2.0988e-12), (90, 2.0919e-12), (91, 2.0851e-12), (92, 2.0786e-12), (93, 2.0721e-12),
  (94, 2.0659e-12), (95, 2.0598e-12), (96, 2.0538e-12), (97, 2.0480e-12), (98, 2.0423e-12),
  (99, 2.0367e-12), (100, 2.0339e-12), (110, 1.9853e-12), (120, 1.9457e-12), (130, 1.9126e-12),
  (140, 1.8847e-12), (150, 1.8608e-12), (160, 1.8401e-12), (170, 1.8219e-12), (180, 1.8059e-12),
  (190, 1.7917e-12), (200, 1.7789e-12), (210, 1.7675e-12), (220, 1.7571e-12), (230, 1.7476e-12),
  (240, 1.7390e-12), (250, 1.7311e-12), (260, 1.7238e-12), (270, 1.7171e-12), (280, 1.7108e-12),
  (290, 1.7051e-12), (300, 1.6997e-12), (310, 1.6946e-12), (320, 1.6899e-12), (330, 1.6855e-12),
  (340, 1.6814e-12), (350, 1.6775e-12), (360, 1.6738e-12), (370, 1.6703e-12), (380, 1.6670e-12), (390, 1.6639e-12),
  (400, 1.6609e-12), (410, 1.6581e-12), (420, 1.6554e-12), (430, 1.6529e-12), (440, 1.6505e-12),
  (450, 1.6481e-12), (475, 1.6428e-12), (500, 1.6380e-12), (525, 1.6336e-12), (550, 1.6296e-12),
  (575, 1.6260e-12), (600, 1.6227e-12), (625, 1.6197e-12), (650, 1.6169e-12), (675, 1.6143e-12),
  (700, 1.6119e-12), (725, 1.6097e-12), (750, 1.6076e-12), (775, 1.6057e-12), (800, 1.6038e-12),
  (825, 1.6021e-12), (850, 1.6005e-12), (875, 1.5990e-12), (900, 1.5976e-12), (925, 1.5962e-12),
  (950, 1.5949e-12), (975, 1.5937e-12), (1000, 1.5925e-12), (1025, 1.5914e-12), (1050, 1.5904e-12),
  (1075, 1.5894e-12), (1100, 1.5885e-12), (1125, 1.5875e-12), (1150, 1.5867e-12), (1175, 1.5858e-12),
  (1200, 1.5850e-12), (1225, 1.5843e-12), (1250, 1.5836e-12), (1275, 1.5828e-12), (1300, 1.5822e-12),
  (1325, 1.5815e-12), (1350, 1.5809e-12), (1375, 1.5803e-12), (1400, 1.5797e-12), (1425, 1.5791e-12),
  (1450, 1.5786e-12), (1475, 1.5781e-12), (1500, 1.5776e-12), (1525, 1.5771e-12), (1550, 1.5766e-12),
  (1575, 1.5761e-12), (1600, 1.5757e-12), (1625, 1.5753e-12), (1650, 1.5749e-12), (1675, 1.5745e-12),
  (1700, 1.5741e-12), (1725, 1.5737e-12), (1750, 1.5733e-12), (1775, 1.5729e-12), (1800, 1.5726e-12),
  (1825, 1.5723e-12), (1850, 1.5719e-12), (1875, 1.5716e-12), (1900, 1.5713e-12), (1925, 1.5710e-12),
  (1950, 1.5707e-12), (1975, 1.5704e-12), (2000, 1.5701e-12), (2100, 1.3254e-12), (2200, 7.1013e-13),
  (2300, 3.8078e-13), (2400, 2.0436e-13), (2500, 1.0977e-13), (2600, 5.9004e-14), (2700, 3.1743e-14),
  (2800, 1.7095e-14), (2900, 9.2127e-15), (3000, 4.9698e-15), (3100, 2.6833e-15), (3200, 1.4502e-15),
  (3300, 7.8459e-16), (3400, 4.2495e-16), (3500, 2.3044e-16), (3600, 1.2511e-16), (3700, 6.8015e-17),
  (3800, 3.7027e-17), (3900, 2.0187e-17), (4000, 1.1024e-17), (4100, 6.0301e-18), (4200, 3.3046e-18),
  (4300, 1.8146e-18), (4400, 9.9846e-19), (4500, 5.5065e-19), (4600, 3.0441e-19), (4700, 1.6903e-19),
  (4800, 9.4404e-20), (4900, 5.3026e-20), (5000, 2.9949e-20), (6000, 1.2979e-22), (7000, 8.5175e-25),
  (8000, 7.7862e-27), (9000, 9.2230e-29), (10000, 1.3682e-30), (20000, 1.9349e-45), (30000, 6.6592e-57),
  (40000, 1.3470e-66), (50000, 3.7292e-75), (60000, 6.6648e-83), (70000, 4.9112e-90), (80000, 1.1133e-96),
  (90000, 6.3306e-103), (100000, 7.7825e-109), (200000, 1.2375e-156), (300000, 2.1902e-193), (400000, 2.1118e-224),
  (500000, 9.5685e-252), (600000, 1.7723e-276), (700000, 3.1360e-299), (800000, 2.0569e-320),
  (900000, 2.5885e-340), (1e6, 3.8635e-359), (1e7, 1.0364e-1153)
]

/-- Table 5.  Sample of values showing $\eps_{\pi, asymp}(x_1)$ interpolates an upper bound for $\eps_{\pi,num}(x_1)$ with $A_\pi = 121.107$, $B = 3.2$, and $C = 2$.  See Corollary 22.  Note that values $\eps_{\pi, num}(x_1,\infty)$ displayed are computed using (12) from Theorem 6 rather than Corollary 8. -/
def Table_5 : List (ℝ × ℝ × ℝ) := [
  (100, 1.9202, 2.0495e-12),
  (1000, 6.6533e-7, 1.5938e-12),
  (2000, 2.8341e-11, 1.5707e-12),
  (3000, 1.0385e-14, 4.9711e-15),
  (4000, 1.2145e-17, 1.1026e-17),
  (5000, 3.0305e-20, 2.9954e-20),
  (6000, 1.3052e-22, 1.2980e-22),
  (7000, 8.5363e-25, 8.5185e-25),
  (8000, 7.7910e-27, 7.7871e-27),
  (9000, 9.3522e-29, 9.2236e-29),
  (10000, 1.4137e-30, 1.3683e-30),
  (11000, 2.6036e-32, 2.4758e-32),
  (12000, 5.6934e-34, 5.3287e-34),
  (13000, 1.4481e-35, 1.3361e-35),
  (14000, 4.2127e-37, 3.8368e-37),
  (15000, 1.3824e-38, 1.2443e-38),
  (16000, 5.0581e-40, 4.5033e-40),
  (17000, 2.0432e-41, 1.8009e-41),
  (18000, 9.0354e-43, 7.8897e-43),
  (19000, 4.3424e-44, 3.7589e-44),
  (20000, 2.2536e-45, 1.9349e-45)
]
/-- **FKS2 Corollary 22**

One has
  $$
  |\pi(x) - \mathrm{Li}(x)| \leq 9.2211 x \sqrt{\log x} \exp(-0.8476 \sqrt{\log x})
  $$
  for all $x \geq 2$.

PROVIDED SOLUTION:
We fix $R = 1$, $x_0 = 2$, $x_1 = e^{100}$, $A_\theta = 9.2211$, $B = 1.5$ and $C = 0.8476$. By Corollary \ref{fks2-corollary-14}, these are admissible for all $x \geq 2$, so we can apply Theorem \ref{fks2-theorem-3} and calculate that
  $$
  \mu_{asymp}(40.78\ldots, e^{20000}) \leq 5.01516 \cdot 10^{-5}.
  $$
  This implies that $A_\pi = 121.103$ is admissible for all $x \geq e^{20000}$.

  As in the proof of [reference] one may verify that the numerical results obtainable from Theorem \ref{fks2-theorem-6}, using Corollary \ref{fks2-corollary-8}, may be interpolated as a step function to give a bound on $E_\pi(x)$ of the shape $\varepsilon_{\pi,asymp}(x)$. In this way we obtain that $A_\pi = 121.107$ is admissible for $x > 2$. Note that the subdivisions we use are essentially the same as used in [reference]. In Table 5 we give a sampling of the relevant values, more of the values of $\varepsilon_{\pi,num}(x_1)$ can be found in Table 4. Far more detailed versions of these tables will be posted online in https://arxiv.org/src/2206.12557v1/anc/PrimeCountingTables.pdf.
-/
theorem corollary_22 : Eπ.classicalBound 9.2211 1.5 0.8476 1 2 := sorry


def table6 : List (List ℝ) := [[0.000120, 0.25, 1.00, 22.955],
                                 [0.826, 0.25, 1.00, 1.000],
                                 [1.41, 0.50, 1.50, 2.000],
                                 [1.76, 1.00, 1.50, 3.000],
                                 [2.22, 1.50, 1.50, 3.000],
                                 [12.4, 1.50, 1.90, 1.000],
                                 [38.8, 1.50, 1.95, 1.000],
                                 [121.107, 1.50, 2.00, 1.000],
                                 [6.60, 2.00, 2.00, 3.000]]
/-- **FKS2 Corollary 23**

$A_\pi, B, C, x_0$ as in [reference] give an admissible asymptotic bound for $E_\pi$ with
  $R = 5.5666305$.

PROVIDED SOLUTION:
The bounds of the form $\eps_{\pi, asymp}(x)$ come from selecting a value $A$ for which Corollary \ref{fks-corollary-22} provides a better bound at $x = e^{7500}$ and from verifying that the bound in Corollary \ref{fks-corollary-22} decreases faster beyond this point. This final verification proceeds by looking at the derivative of the ratio as in Lemma \ref{fks-lemma-10}. To verify these still hold for smaller $x$, we proceed as below. To verify the results for any $x$ in $\log(10^{19}) < \log(x) < 100000$, one simply proceeds as in [reference] and interpolates the numerical results of Theorem \ref{fks2-theorem-6}. For instance, we use the values in Table 4 as a step function and verifies that it provides a tighter bound than we are claiming. Note that our verification uses a more refined collection of values than those provided in Table 4 or the tables posted online in https://arxiv.org/src/2206.12557v1/anc/PrimeCountingTables.pdf. To verify results for $x < 10^{19}$, one compares against the results from Theorem \ref{buthe-theorem-2a}, or one checks directly for particularly small $x$.
-/
theorem corollary_23 (Aπ B C x₀ : ℝ) (h : [Aπ, B, C, x₀] ∈ table6) :
    Eπ.classicalBound Aπ B C 5.5666305 x₀ := sorry


noncomputable def table7 : List ((ℝ → ℝ) × Set ℝ) :=
  [ (fun x ↦ 2 * log x * x^(-(1:ℝ)/2), Set.Icc 1 57),
    (fun x ↦ (log x)^(3/2) * x^(-(1:ℝ)/2), Set.Icc 1 65.65),
    (fun x ↦ 8 * π * (log x)^2 * x^(-(1:ℝ)/2), Set.Icc 8 60.8),
    (fun x ↦ (log x)^2 * x^(-(1:ℝ)/2), Set.Icc 1 70.6),
    (fun x ↦ (log x)^3 * x^(-(1:ℝ)/2), Set.Icc 1 80),
    (fun x ↦ x^(-(1:ℝ)/3), Set.Icc 1 80.55),
    (fun x ↦ x^(-(1:ℝ)/4), Set.Icc 1 107.6),
    (fun x ↦ x^(-(1:ℝ)/5), Set.Icc 1 134.8),
    (fun x ↦ x^(-(1:ℝ)/10), Set.Icc 1 270.8),
    (fun x ↦ x^(-(1:ℝ)/50), Set.Icc 1 1358.6),
    (fun x ↦ x^(-(1:ℝ)/100), Set.Icc 1 3757.6)
  ]
/-- **FKS2 Corollary 24**

We have the bounds $E_\pi(x) \leq B(x)$, where
  $B(x)$ is given by Table 7.

PROVIDED SOLUTION:
Same as in Corollary \ref{fks-corollary-23}.
-/
theorem corollary_24 (B : ℝ → ℝ) (I : Set ℝ) (h : (B, I) ∈ table7) :
    ∀ x, log x ∈ I → Eπ x ≤ B x := sorry

/-- **FKS2 Corollary 26**

One has
  $$
  |\pi(x) - \mathrm{Li}(x)| \leq 0.4298 \frac{x}{\log x}
  $$
  for all $x \geq 2$.

PROVIDED SOLUTION:
We numerically verify that the inequality holds by showing that, for $1 \leq n \leq 25$ and all $x \in [p_n, p_{n+1}]$,
  $$
  \left| \frac{\log(x)}{x} (\pi(x) - \mathrm{Li}(x)) \right| \leq \left| \frac{\log(p_n)}{p_n} (\pi(p_n) - \mathrm{Li}(p_{n+1})) \right| \leq 0.4298.
  $$
  For $x$ satisfying $p_{25} = 97 \leq x \leq 10^{19}$, we use Theorems \ref{buthe-theorem-2e}, \ref{buthe-theorem-2f} and verify
  $$
  \mathcal{E}(x) = \frac{1}{\sqrt{x}} \left( 1.95 + \frac{3.9}{\log(x)} + \frac{19.5}{(\log(x))^2} \right) \leq 0.4298.
  $$
  For $x > 10^{19}$, we use Theorem \ref{fks-theorem-6} as well as values for $\varepsilon_{\pi,num}(x)$ found in Table 4 to conclude
  $$
  \varepsilon_{\pi,num}(x) \leq 0.4298.
  $$
-/
theorem corollary_26 : Eπ.bound 0.4298 2 := sorry


end FKS2
