import Mathlib
import PrimeNumberTheoremAnd.SecondaryDefinitionsAristotle
import PrimeNumberTheoremAnd.FKS2Aristotle
import PrimeNumberTheoremAnd.DusartAristotle

/-!
# Summary of results
-/

/-!
Here we list some papers that we plan to incorporate into this section in the future, and list
some results that have not yet been moved into dedicated paper sections.

References to add:

Dusart [reference]

PT: D. J. Platt and T. S. Trudgian, The error term in the prime number theorem,
Math. Comp. 90 (2021), no. 328, 871–881.

JY: D. R. Johnston, A. Yang, Some explicit estimates for the error term in the prime number
theorem, arXiv:2204.01980.
-/
open Nat hiding log
open Finset Real Chebyshev

namespace PT


def Table_1 : List (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) :=
 [ (1000, 0.98, 461.9, 1.52, 1.89, 1.20e-5),
   (2000, 0.98, 411.4, 1.52, 1.89, 8.35e-10),
   (3000, 0.98, 379.6, 1.52, 1.89, 4.51e-13),
   (4000, 0.98, 356.3, 1.52, 1.89, 7.33e-16),
   (5000, 0.99, 713.0, 1.51, 1.94, 9.77e-19),
   (6000, 0.99, 611.6, 1.51, 1.94, 4.23e-21),
   (7000, 0.99, 590.1, 1.51, 1.94, 3.09e-23),
   (8000, 0.99, 570.5, 1.51, 1.94, 3.12e-25),
   (9000, 0.99, 552.3, 1.51, 1.94, 4.11e-27),
   (10000,0.99,535.4 ,1.51 ,1.94 ,6.78e-29)]
/-- **PT Theorem 1**

Let $R = 5.573412$. For each row $\{X, \sigma, A, B, C, \epsilon_0\}$ from [reference] we have
$$
\left|\frac{\psi(x) - x}{x}\right| \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C\sqrt{\frac{\log x}{R}}\right)
$$
and
\begin{equation*}
\left|\psi(x)-x\right|\leq \epsilon_0 x
\end{equation*}
for all $\log x \geq X$.
-/
theorem theorem_1 (X σ A B C ε₀ : ℝ) (h : (X, σ, A, B, C, ε₀) ∈ Table_1) :
  Eψ.classicalBound A B C 5.573412 (exp X) ∧ Eψ.numericalBound (exp X) (fun _ ↦ ε₀) := by sorry

/-- **PT Corollary 1**

Let $R = 5.573412$. For each row $\{X, \sigma, A, B, C, \epsilon_0\}$ from [reference] we have
$$
\left|\frac{\psi(x) - x}{x}\right| \leq A_1 \left(\frac{\log x}{R}\right)^B \exp\left(-C\sqrt{\frac{\log x}{R}}\right)
$$
where $A_1 = A + 0.1$.

PROVIDED SOLUTION:
This follows trivially (and wastefully) from the work of Dusart  [reference] or the authors [reference].  It should also follow from the results of [reference].
-/
theorem corollary_1 (X σ A B C ε₀ : ℝ) (h : (X, σ, A, B, C, ε₀) ∈ Table_1) :
  Eθ.classicalBound (A + 0.1) B C 5.573412 (exp X) := by sorry

/-- **PT Corollary 2**

One has
  $$
  |\pi(x) - \mathrm{Li}(x)| \leq 235 x (\log x)^{0.52} \exp(-0.8 \sqrt{\log x})
  $$
  for all $x \geq \exp(2000)$.
-/
theorem corollary_2 : Eπ.classicalBound 235 1.52 0.8 1 (exp 2000) := by
  admit

end PT
/-- **JY Corollary 1.3**

One has
  $$
  |\pi(x) - \mathrm{Li}(x)| \leq 9.59 x (\log x)^{0.515} \exp(-0.8274 \sqrt{\log x})
  $$
  for all $x \geq 2$.
-/
theorem JY.corollary_1_3 : Eπ.classicalBound 9.59 1.515 0.8274 1 2 := by
  admit

/-- **JY Theorem 1.4**

One has
  $$
  |\pi(x) - \mathrm{Li}(x)| \leq 0.028 x (\log x)^{0.801}
    \exp(-0.1853 \log^{3/5} x / (\log \log x)^{1/5}))
  $$
  for all $x \geq 2$.
-/
theorem JY.theorem_1_4 : Eπ.vinogradovBound 0.028 0.801 0.1853 23 := sorry


/-!
TODO: input other results from JY
-/

/-!
The results below are taken from https://tme-emt-wiki-gitlab-io-9d3436.gitlab.io/Art09.html
-/
/-- **Schoenfeld 1976**

If $x > 2010760$, then there is a prime in the interval
  $$
  \left( x\left(1 - \frac{1}{15697}\right), x \right].
  $$
-/
theorem Schoenfeld1976.has_prime_in_interval (x h : ℝ) (hx : x > 2010759.9) :
  HasPrimeInInterval x (x/15697) := by sorry

/-- **Ramaré-Saouter 2003**

If $x > 10,726,905,041$, then there is a prime in the interval $(x(1-1/28314000), x]$.
-/
theorem RamareSaouter2003.has_prime_in_interval (x : ℝ) (hx : x > 10726905041) :
    HasPrimeInInterval (x*(1-1/28314000)) (x/28314000) := by sorry

/-- **Ramaré-Saouter 2003 (2)**

If $x > \exp(53)$, then there is a prime in the interval
  $$ \left( x\left(1 - \frac{1}{204879661}\right), x \right]. $$
-/
theorem RamareSaouter2003.has_prime_in_interval_2 (x : ℝ) (hx : x > exp 53) :
    HasPrimeInInterval (x*(1-1/204879661)) (x/204879661) := by sorry

/-- **Gourdon-Demichel 2004**

If $x > \exp(60)$, then there is a prime in the interval
  $$ \left( x\left(1 - \frac{1}{14500755538}\right), x \right]. $$
-/
theorem GourdonDemichel2004.has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/14500755538)) (x/14500755538) := by sorry

/-- **Prime Gaps 2014**

If $x > \exp(60)$, then there is a prime in the interval
  $$ \left( x\left(1 - \frac{1}{1966196911}\right), x \right]. $$
-/
theorem PrimeGaps2014.has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/1966196911)) (x/1966196911) := by sorry

/-- **Prime Gaps 2024**

If $x > \exp(60)$, then there is a prime in the interval
  $$ \left( x\left(1 - \frac{1}{76900000000}\right), x \right]. $$
-/
theorem PrimeGaps2024.has_prime_in_interval (x : ℝ) (hx : x > exp 60) :
    HasPrimeInInterval (x*(1-1/76900000000)) (x/76900000000) := by sorry

/-- **Trudgian 2016**

If $x > 2,898,242$, then there
  is a prime in the interval
  $$ \left[ x, x\left(1 + \frac{1}{111(\log x)^2}\right) \right]. $$
-/
theorem Trudgian2016.has_prime_in_interval (x : ℝ) (hx : x > 2898242) :
    HasPrimeInInterval x (x / (111 * (log x) ^ 2)) := by sorry

/-- **Dudek 2014**

If $x > \exp(\exp(34.32))$, then there is a prime in the interval
  $$ \left( x, x + 3x^{2/3} \right]. $$
-/
theorem Dudek2014.has_prime_in_interval (x : ℝ) (hx : x > exp (exp 34.32)) :
    HasPrimeInInterval x (3 * x ^ (2 / 3 : ℝ)) := by sorry

/-- **Cully-Hugill 2021**

If $x > \exp(\exp(33.99))$, then there is a prime in the interval
  $$ \left( x, x + 3x^{2/3} \right]. $$
-/
theorem CullyHugill2021.has_prime_in_interval (x : ℝ) (hx : x > exp (exp 33.99)) :
    HasPrimeInInterval x (3 * x ^ (2 / 3 : ℝ)) := by sorry

/-- **RH Prime Interval 2002**

Assuming the Riemann Hypothesis, for $x \geq 2$, there is a prime in the interval
  $$ \left( x - \frac{8}{5}\sqrt{x} \log x, x \right]. $$
-/
theorem RHPrimeInterval2002.has_prime_in_interval (x : ℝ) (hx : x ≥ 2) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (8 / 5) * sqrt x * log x) ((8 / 5) * sqrt x * log x) := by sorry

/-- **Dudek 2015 under RH**

Assuming the Riemann Hypothesis, for $x \geq 2$, there is a prime in the interval
  $$ \left( x - \frac{4}{\pi}\sqrt{x} \log x, x \right]. $$
-/
theorem Dudek2015RH.has_prime_in_interval (x : ℝ) (hx : x ≥ 2) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (4 / π) * sqrt x * log x) ((4 / π) * sqrt x * log x) := by sorry

/-- **Carneiro et al. 2019 under RH**

Assuming the Riemann Hypothesis, for $x \geq 4$, there is a prime in the interval
  $$ \left( x - \frac{22}{25}\sqrt{x}\log x, x \right]. $$
-/
theorem CarneiroEtAl2019RH.has_prime_in_interval (x : ℝ) (hx : x ≥ 4) (RH : RiemannHypothesis) :
    HasPrimeInInterval (x - (22 / 25) * sqrt x * log x) ((22 / 25) * sqrt x * log x) := by sorry


namespace KadiriLumley

noncomputable def Table_2 : List (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ ) :=
  [(log (4 * 10 ^ 18), 5, 3.580e-8, 272519712, 0.92, 0.2129, 36082898),
   (43, 5, 3.349e-8, 291316980, 0.92, 0.2147, 38753947),
   (44, 6, 2.330e-8, 488509984, 0.92, 0.2324, 61162616),
   (45, 7, 1.628e-8, 797398875, 0.92, 0.2494, 95381241),
   (46, 8, 1.134e-8, 1284120197, 0.92, 0.2651, 148306019),
   (47, 9, 8.080e-9, 1996029891, 0.92, 0.2836, 227619375),
   (48, 11, 6.000e-9, 3204848430, 0.93, 0.3050, 346582570),
   (49, 15, 4.682e-9, 5415123831, 0.93, 0.3275, 518958776),
   (50, 20, 3.889e-9, 8466793105, 0.93, 0.3543,753575355),
   (51 ,28 ,3.625e-9 ,12399463961 ,0.93 ,0.3849 ,1037917449),
   (52 ,39 ,3.803e-9 ,16139006408 ,0.93 ,0.4127 ,1313524036),
   (53 ,48 ,4.088e-9 ,18290358817 ,0.93 ,0.4301 ,1524171138),
   (54 ,54 ,4.311e-9 ,19412056863 ,0.93 ,0.4398 ,1670398039),
   (55 ,56 ,4.386e-9 ,19757119193 ,0.93 ,0.4445 ,1770251249),
   (56 ,59 ,4.508e-9 ,20210075547 ,0.93 ,0.4481 ,1838818070),
   (57 ,59 ,4.506e-9 ,20219045843 ,0.93 ,0.4496 ,1886389443),
   (58 ,61 ,4.590e-9 ,20495459359 ,0.93 ,0.4514 ,1920768795),
   (59 ,61 ,4.589e-9 ,20499925573 ,0.93 ,0.4522 ,1946282821),
   (60 ,61 ,4.588e-9 ,20504393735 ,0.93 ,0.4527 ,1966196911),
   (150, 64, 4.685e-9, 21029543983, 0.96, 0.4641, 2442159714)]
/-- **Kadiri-Lumley Prime Gaps**

[reference] If $(\log x_0, m, \delta, T_1, \sigma_0, a, \Delta)$ is a row [reference], then for all $x \geq x_0$, there is a prime between $x(1-\Delta^{-1})$ and $x$.
-/
theorem has_prime_in_interval (x₀ x m δ T₁ σ₀ a Δ : ℝ) (hx : x ≥ x₀) (hrow : (log x₀, m, δ, T₁, σ₀, a, Δ) ∈ Table_2) :
    HasPrimeInInterval (x*(1-Δ⁻¹)) (x/Δ) := by sorry


end KadiriLumley
