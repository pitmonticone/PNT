import Mathlib
import PrimeNumberTheoremAnd.SecondaryDefinitionsAristotle

/-!
# Converting prime number theorems to prime in short interval theorems



In this section, bounds on $E_\theta$ are used to deduce the existence of primes in short intervals. (One could also proceed using $E_\pi$, but the bounds are messier and the results slightly weaker.)
-/

open Real Chebyshev Nat Finset
/-- **Increase in pi iff prime in short interval**

There is a prime in $(x, x+h]$ iff $\pi(x+h) > \pi(x)$.

PROVIDED SOLUTION:
Both are equivalent to $\sum_{x < p \leq x+h} 1 > 0$.
-/
lemma HasPrimeInInterval.iff_pi_ge (x h : ℝ) : HasPrimeInInterval x h ↔ pi (x + h) > pi x := by
  admit

-- this is a legacy piece of code that could be incorporated somehow into the proof of `HasPrimeInInterval.iff_theta_ge` below.

theorem theta_pos_implies_prime_in_interval {x y : ℝ} (_hxy : y < x) (h : θ x - θ y > 0) :
    HasPrimeInInterval y (x - y) := by
  admit

/-- **Increase in theta iff prime in short interval**

There is a prime in $(x, x+h]$ iff $\theta(x+h) > \theta(x)$.

PROVIDED SOLUTION:
Both are equivalent to $\sum_{x < p \leq x+h} \log p > 0$.
-/
lemma HasPrimeInInterval.iff_theta_ge (x h : ℝ) : HasPrimeInInterval x h ↔ θ (x + h) > θ x := by
  admit

/-- **Upper bound on Etheta implies prime in short interval**

There is a prime in $(x, x+h]$ if $x E_\theta(x) + (x+h) E_\theta(x+h) < h$.

PROVIDED SOLUTION:
Lower bound $\theta(x+h) - \theta(x)$ using $\theta(x+h) \geq x+h (1 - E_\theta(x+h))$ and $\theta(x) \leq x (1 + E_\theta(x))$ and apply Lemma \ref{theta-inc}.
-/
lemma Eθ.hasPrimeInInterval (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    x * Eθ x + (x + h) * Eθ (x + h) < h → HasPrimeInInterval x h := by
  admit

/-- **Numerical bound on Etheta implies prime in short interval**

If $E_\theta(x) \leq \varepsilon(x_0)$ for all $x \geq x_0$, and $(2x+h) \varepsilon(x_0)  < h$, then there is a prime in $(x, x+h]$.

PROVIDED SOLUTION:
Apply Lemma \ref{etheta-pi}.
-/
lemma Eθ.numericalBound.hasPrimeInInterval {x₀ x h : ℝ} {ε : ℝ → ℝ} (hEθ : Eθ.numericalBound x₀ ε)
    (hh : 0 < h) (hx₀ : x₀ ≤ x) (hx : 0 < x) (hε : (2 * x + h) * ε x₀ < h) :
    HasPrimeInInterval x h := by
  admit

/-- **Classical bound on Etheta implies prime in short interval**

If $E_\theta(x)$ enjoys a classical bound for all $x \geq x_0$, $x \geq \exp( R (2B/C)^2 )$ and $(2x+h) A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right) < h$, then there is a prime in $(x, x+h]$.

PROVIDED SOLUTION:
Apply Lemma \ref{etheta-num-pi} and Lemma \ref{classical-to-numeric}.
-/
lemma Eθ.classicalBound.hasPrimeInInterval {x₀ x h A B C R : ℝ} (hEθ : Eθ.classicalBound A B C R x₀)
  (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hR : 0 < R) (hh : 0 < h) (hx : x₀ ≤ x) (hx' : x ≥ exp (R * (2 * B / C) ^ 2))
  (hb : (2 * x + h) * (admissible_bound A B C R x) < h) :
    HasPrimeInInterval x h := by
  admit

/-- **Prime gap record implies prime in short interval**

If there is a prime gap record $(g,p)$, then there is a prime in $(x,x+h]$ whenever $x < p$ and $h \geq g$.

PROVIDED SOLUTION:
If $p_k$ is the largest prime less than or equal to $x$, then $p_{k+1} - p_k < g \leq h$, hence $x < p_{k+1} \leq x+h$, giving the claim.
-/
lemma prime_gap_record.hasPrimeInInterval {g p : ℕ} {x h : ℝ} (hgap : prime_gap_record p g) (hx : x ≤ p) (hx_ge_two : x ≥ 2) (hh : h ≥ g) :
    HasPrimeInInterval x h := by
  admit