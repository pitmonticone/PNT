import Mathlib
import PrimeNumberTheoremAnd.SecondaryDefinitionsAristotle

open Chebyshev Finset Nat Real Filter

/-!
# An inequality of Costa-Pereira



We record here an inequality relating the Chebyshev functions $\psi(x)$ and $\theta(x)$ due to
Costa Pereira [reference], namely
$$ \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/7}) \leq \psi(x) - \theta(x) \leq \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5}) . $$
-/

namespace CostaPereira
/-- **Costa-Pereira Sublemma 1.1**

For every $x > 0$ we have $\psi(x) = \sum_{k \geqslant 1} \theta(x^{1/k})$.

PROVIDED SOLUTION:
This follows directly from the definitions of $\psi$ and $\theta$.
-/
theorem sublemma_1_1 {x : ℝ} (hx : 0 < x) : ψ x = ∑' (k : ℕ), θ (x ^ (1 / ((k.succ : ℕ) : ℝ))) := by
  admit

/-- **Costa-Pereira Sublemma 1.2**

For every $x > 0$ and $n$ we have $\psi(x^{1/n}) = \sum_{k \geqslant 1} \theta(x^{1/nk})$.

PROVIDED SOLUTION:
Follows from Sublemma \ref{costa-pereira-sublemma-1-1} and substitution.
-/
theorem sublemma_1_2 {x : ℝ} (hx : 0 < x) (n : ℝ) :
    ψ (x ^ (1 / n : ℝ)) = ∑' (k : ℕ), θ (x ^ (1 / (n * ((k.succ : ℕ) : ℝ)))) := by
  admit

/-- **Costa-Pereira Sublemma 1.3**

For every $x > 0$ we have
  $$
  \psi(x) = \theta(x) + \psi(x^{1/2}) + \sum_{k \geqslant 1} \theta(x^{1/(2k+1)}).
  $$

PROVIDED SOLUTION:
Follows from Sublemma \ref{costa-pereira-sublemma-1-1} and Sublemma \ref{costa-pereira-sublemma-1-2}.
-/
theorem sublemma_1_3 {x : ℝ} (hx : 0 < x) :
    ψ x = θ x + ψ (x ^ (1 / 2 : ℝ)) + ∑' (k : ℕ), θ (x ^ (1 / (2 * (k.succ : ℝ) + 1))) := by
  admit

/-- **Costa-Pereira Sublemma 1.4**

For every $x > 0$ we have
  $$
  \psi(x) - \theta(x) = \psi(x^{1/2}) + \sum_{k \geqslant 1} \theta(x^{1/(6k-3)}) + \sum_{k \geqslant 1} \theta(x^{1/(6k-1)}) + \sum_{k \geqslant 1} \theta(x^{1/(6k+1)}).
  $$

PROVIDED SOLUTION:
Follows from Sublemma \ref{costa-pereira-sublemma-1-3} and rearranging the sum.
-/
theorem sublemma_1_4 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x = ψ (x ^ (1 / 2 : ℝ)) +
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ : ℕ) : ℝ) - 3))) +
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ : ℕ) : ℝ) - 1))) +
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ : ℕ) : ℝ) + 1))) := by
  admit

/-- **Costa-Pereira Sublemma 1.5**

For every $x > 0$ we have
  $$
  \psi(x^{1/3}) = \sum_{k \geqslant 1} \theta(x^{1/(6k-3)}) + \sum_{k \geqslant 1} \theta(x^{1/(6k)}).
  $$

PROVIDED SOLUTION:
Follows from Sublemma \ref{costa-pereira-sublemma-1-2} and substitution.
-/
theorem sublemma_1_5 {x : ℝ} (hx : 0 < x) :
    ψ (x ^ (1 / 3 : ℝ)) = ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ : ℕ) : ℝ) - 3))) +
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ : ℕ) : ℝ)))) := by
  admit

/-- **Costa-Pereira Sublemma 1.6**

For every $x > 0$ we have
  $$
  \psi(x) - \theta(x) = \psi(x^{1/2}) + \psi(x^{1/3}) + \sum_{k \geqslant 1} \theta(x^{1/(6k-1)}) - \sum_{k \geqslant 1} \theta(x^{1/(6k)}) + \sum_{k \geqslant 1} \theta(x^{1/(6k+1)}).
  $$

PROVIDED SOLUTION:
Follows from Sublemma \ref{costa-pereira-sublemma-1-4} and Sublemma \ref{costa-pereira-sublemma-1-5}.
-/
theorem sublemma_1_6 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x =
      ψ (x ^ (1 / 2:ℝ)) +
      ψ (x ^ (1 / 3:ℝ)) +
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ  : ℕ) : ℝ) - 1))) -
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ  : ℕ) : ℝ)))) +
      ∑' (k : ℕ), θ (x ^ (1 / (6 * ((k.succ  : ℕ) : ℝ) + 1))) := by
  admit

/-- **Costa-Pereira Sublemma 1.7**

For every $x > 0$ we have
  $$
  \psi(x) - \theta(x) \leqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \sum_{k \geqslant 1} \theta(x^{1/5k}
  $$

PROVIDED SOLUTION:
Follows from Sublemma \ref{costa-pereira-sublemma-1-6} and the fact that $\theta$
  is an increasing function.
-/
theorem sublemma_1_7 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≤ ψ (x ^ (1 / 2 : ℝ)) + ψ (x ^ (1 / 3 : ℝ)) + ∑' (k : ℕ), θ (x ^ (1 / (5 * ((k.succ  : ℕ) : ℝ)))) := by
  admit

/-- **Costa-Pereira Sublemma 1.8**

For every $x > 0$ we have
  $$
  \psi(x) - \theta(x) \geqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \sum_{k \geqslant 1} \theta(x^{1/7k}
  $$

PROVIDED SOLUTION:
Follows from Sublemma \ref{costa-pereira-sublemma-1-6} and the fact that $\theta$
  is an increasing function.
-/
theorem sublemma_1_8 {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≥ ψ (x ^ (1 / 2 : ℝ)) + ψ (x ^ (1 / 3 : ℝ)) + ∑' (k : ℕ), θ (x ^ (1 / (7 * ((k.succ : ℕ) : ℝ)))) := by
  admit

/-- **Costa-Pereira Theorem 1a**

For every $x > 0$ we have
  $\psi(x) - \theta(x) \leqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5})$.

PROVIDED SOLUTION:
Follows from Sublemma \ref{costa-pereira-sublemma-1-7} and
  Sublemma \ref{costa-pereira-sublemma-1-2}.
-/
theorem theorem_1a {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≤ ψ (x ^ (1 / 2 : ℝ)) + ψ (x ^ (1 / 3 : ℝ)) + ψ (x ^ (1 / 5 : ℝ)) := by
  admit

/-- **Costa-Pereira Theorem 1b**

For every $x > 0$ we have
  $\psi(x) - \theta(x) \geqslant \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/7})$.

PROVIDED SOLUTION:
Follows from Sublemma \ref{costa-pereira-sublemma-1-8} and
  Sublemma \ref{costa-pereira-sublemma-1-2}.
-/
theorem theorem_1b {x : ℝ} (hx : 0 < x) :
    ψ x - θ x ≥ ψ (x ^ (1 / 2 : ℝ)) + ψ (x ^ (1 / 3 : ℝ)) + ψ (x ^ (1 / 7 : ℝ)) := by
  admit

end CostaPereira
