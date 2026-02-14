import Mathlib
import PrimeNumberTheoremAnd.LogTablesAristotle
import PrimeNumberTheoremAnd.SecondaryDefinitionsAristotle

/-!
# Chebyshev's estimates



We record Chebyshev's estimates on $\psi$. The material here is adapted from the presentation of Diamond [reference].
-/

namespace Chebyshev

open Real
open ArithmeticFunction hiding log
/-- **The function $T$**

$T(x) := \sum_{n \leq x} \log n$.
-/
noncomputable def T (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, log n
/-- **Upper bound on $T$**

For $x \geq 1$, we have $T(x) \leq x \log x - x + 1 + \log x$.

PROVIDED SOLUTION:
Upper bound $\log n$ by $\int_n^{n+1} \log t\ dt$ for $n < x-1$ and by $\log x$ for $x-1 < n \leq x$ to bound
  $$T(x) \leq \int_1^x \log t\ dt + \log x$$
  giving the claim.
-/
theorem T.le (x : ℝ) (hx : 1 ≤ x) : T x ≤ x * log x - x + 1 + log x := by
  admit

/-- **Lower bound on $T$**

For $x \geq 1$, we have $T(x) \geq x \log x - x + 1 - \log x$.

PROVIDED SOLUTION:
Drop the $n=1$ term. Lower bound $\log n$ by $\int_{n-1}^{n} \log t\ dt$ for $2 \leq n < x$ to bound
  $$T(x) \geq \int_1^{\lfloor x \rfloor} \log t\ dt \geq \int_1^x \log t\ dt - \log x $$
  giving the claim.
-/
theorem T.ge (x : ℝ) (hx : 1 ≤ x) : T x ≥ x * log x - x + 1 - log x := by
  admit

/-- **Relating $T$ and von Mangoldt**

For $x \geq 0$, we have $T(x) = \sum_{n \leq x} \Lambda(n) \lfloor x/n \rfloor$.

PROVIDED SOLUTION:
This follows from the identity $\log n = \sum_{d|n} \Lambda(d)$ and rearranging sums.
-/
theorem T.eq_sum_Lambda (x : ℝ) : T x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  admit

/-- **$E$ function**

If $\nu : \N \to \R$, let $E: \R \to \R$ denote the function $E(x):= \sum_m \nu(m) \lfloor x / m \rfloor$.
-/
noncomputable def E (ν : ℕ →₀ ℝ) (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * ⌊ x / m ⌋₊)
/-- **Relating a weighted sum of $T$ to an $E$-weighted sum of von Mangoldt**

If $\nu : \N \to \R$ is finitely supported, then
$$ \sum_m \nu(m) T(x/m) = \sum_{n \leq x} E(x/n) \Lambda(n).$$
-/
theorem T.weighted_eq_sum (ν : ℕ →₀ ℝ) (x : ℝ) : ν.sum (fun m w ↦ w * T (x/m)) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * E ν (x/n) := by
  admit

open Finsupp in
/-- **Chebyshev's weight $\nu$**

$\nu = e_1 - e_2 - e_3 - e_5 + e_{30}$, where $e_n$ is the Kronecker delta at $n$.
-/
noncomputable def ν : ℕ →₀ ℝ := single 1 1 - single 2 1 - single 3 1 - single 5 1 + single 30 1
/-- **Cancellation property of $\nu$**

One has $\sum_n \nu(n)/n = 0$

PROVIDED SOLUTION:
This follows from direct computation.
-/
theorem nu_sum_div_eq_zero : ν.sum (fun n w ↦ w / n) = 0 := by
  admit

/-- **$E$ initially constant**

One has $E(x)=1$ for $1 \leq x < 6$.

PROVIDED SOLUTION:
This follows from direct computation.
-/
theorem E_nu_eq_one (x : ℝ) (hx : x ∈ Set.Ico 1 6) : E ν x = 1 := by
  admit

/-- **$E$ is periodic**

One has $E(x+30) = E(x)$.

PROVIDED SOLUTION:
This follows from direct computation.
-/
theorem E_nu_period (x : ℝ) (hx : x ≥ 0) : E ν (x + 30) = E ν x := by
  admit

/-- **$E$ lies between $0$ and $1$**

One has $0 \leq E(x) \leq 1$ for all $x \geq 0$.

PROVIDED SOLUTION:
This follows from direct computation for $0 \leq x < 30$, and then by periodicity for larger $x$.
-/
theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by
  admit

/-- **The $U$ function**

We define $U(x) := \sum_m \nu(m) T(x/m)$.
-/
noncomputable def U (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * T (x/m))
/-- **Lower bounding $\\psi$ by a weighted sum of $T$**

For any $x > 0$, one has $\psi(x) \geq U(x)$.

PROVIDED SOLUTION:
Use Lemma \ref{cheby-T-E} and Lemma \ref{cheby-E-val}.
-/
theorem psi_ge_weighted (x : ℝ) (hx : x > 0) : ψ x ≥ U x := by
  admit

/-- **Upper bounding a difference of $\\psi$ by a weighted sum of $T$**

For any $x > 0$, one has $\psi(x) - \psi(x/6) \leq U(x)$.

PROVIDED SOLUTION:
Use Lemma \ref{cheby-T-E}, Lemma \ref{cheby-E-val}, and Lemma \ref{cheby-E-1}.
-/
theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by
  admit

/-- **The constant $a$**

We define $a := -\sum_m \nu(m) \log m / m$.
-/
noncomputable def a : ℝ := - ν.sum (fun m w ↦ w * log m / m)

lemma a_simpl : a = (7/15) * Real.log 2 + (3/10) * Real.log 3 + (1/6) * Real.log 5 := by
  admit

/-- **Numerical value of $a$**

We have $0.92129 \leq a \leq 0.92130$.
-/
theorem a_bound : a ∈ Set.Icc 0.92129 0.92130 := by
  admit

/-- **Bounds for $U$**

For $x \geq 30$, we have $|U(x) - ax| \leq 5\log x - 5$.

PROVIDED SOLUTION:
Use Lemma \ref{cheby-T-upper}, Lemma \ref{cheby-T-lower}, the definition of $a$, and the triangle inequality, also using that $\log(2)+\log(3)+\log(5)+\log(30) \geq 6$.
-/
theorem U_bound (x : ℝ) (hx : 30 ≤ x) : |U x - a * x| ≤ 5 * log x - 5 := by sorry

/-- **Lower bound for $\\psi$**

For $x \geq 30$, we have $\psi(x) \geq ax - 5\log x - 1$.

PROVIDED SOLUTION:
Use Lemma \ref{U-bounds} and Proposition \ref{cheby-psi-lower}.
-/
theorem psi_lower (x : ℝ) (hx : 30 ≤ x) : ψ x ≥ a * x - 5 * log x + 5 := by
  admit

/-- **Upper bound for $\\psi$ difference**

For $x \geq 30$, we have $\psi(x) - \psi(x/6) \leq ax + 5\log x - 5$.

PROVIDED SOLUTION:
Use Lemma \ref{U-bounds} and Proposition \ref{cheby-psi-upper}.
-/
theorem psi_diff_upper (x : ℝ) (hx : 30 ≤ x) : ψ x - ψ (x / 6) ≤ a * x + 5 * log x - 5 := by
  admit

-- Proof splits into many cases
/-- **Numerical bound for $\\psi(x)$ for very small $x$**

For $0 < x \leq 30$, we have $\psi(x) \leq 1.015 x$.

PROVIDED SOLUTION:
Numerical check (the maximum occurs at $x=19$).  One only needs to check the case when $x$ is a prime power.
-/
theorem psi_num (x : ℝ) (hx : x > 0) (hx2 : x ≤ 30) : ψ x ≤ 1.015 * x := by
  admit

/-- **Upper bound for $\\psi$**

For $x \geq 30$, we have $\psi(x) \leq 6ax/5 + (\log (x/5) / \log 6) (5 \log x - 5)$.

PROVIDED SOLUTION:
Iterate Lemma \ref{psi-diff-upper} using Sublemma \ref{psi-num} .
-/
theorem psi_upper (x : ℝ) (hx : 30 ≤ x) : ψ x ≤ 6 * a * x / 5 + (log (x/5) / log 6) * (5 * log x - 5) := by
  admit

/-- **Numerical bound for $\\psi(x)$ for medium $x$**

For $0 < x \leq 11723$, we have $\psi(x) \leq 1.11 x$.

PROVIDED SOLUTION:
From Lemma \ref{psi-num} we can take $x \geq 30$. If one considers the sequence $x_1,x_2,\dots$ defined by $27, 32, 37, 43, 50, 58, 67, 77, 88, 100, 114, 129, 147, 166, 187, 211, 238, 268, 302, 340, 381, 427, 479, 536, 600, 671, 750, 839, 938, 1048, 1172, 1310, 1464, 1636, 1827, 2041, 2279, 2544, 2839, 3167, 3534, 3943, 4398, 4905, 5471, 6101, 6803, 7586, 8458, 9431, 10515, 11723$ then one should have $\psi(x_{j+1}-1) \leq 1.11 x_j$ for all $j$, which suffices.
-/
theorem psi_num_2 (x : ℝ) (hx : x > 0) (hx2 : x ≤ 11723) : ψ x ≤ 1.11 * x := by sorry

/-- **Clean upper bound for $\\psi$**

For $x > 0$, we have $\psi(x) \leq 1.11 x$.

PROVIDED SOLUTION:
Strong induction on $x$.  For $x \leq 11723$ one can use Sublemma \ref{psi-num-2}.  Otherwise, we can use Proposition \ref{psi-diff-upper} and the triangle inequality.
-/
theorem psi_upper_clean (x : ℝ) (hx : x > 0) : ψ x ≤ 1.11 * x := by sorry


end Chebyshev
