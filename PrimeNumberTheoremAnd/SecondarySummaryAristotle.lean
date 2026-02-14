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

open Finset Nat Real Chebyshev
/-- **PT Corollary 2**

One has
  $$
  |\pi(x) - \mathrm{Li}(x)| \leq 235 x (\log x)^{0.52} \exp(-0.8 \sqrt{\log x})
  $$
  for all $x \geq \exp(2000)$.
-/
theorem PT.corollary_2 : Eπ.classicalBound 235 1.52 0.8 1 (exp 2000) := by
  admit

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
