import Mathlib
import PrimeNumberTheoremAnd.PrimaryDefinitionsAristotle

/-!
# A Lemma involving the M\"obius Function
-/

/-!
In this section we establish a lemma involving sums of the M\"obius function.
-/

namespace MobiusLemma

open ArithmeticFunction Real Finset MeasureTheory Measurable Complex
/-- **Q**

$Q(x)$ is the number of squarefree integers $\leq x$.
-/
noncomputable def Q (x : ℝ) : ℕ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, if Squarefree n then 1 else 0
/-- **R**

$R(x) = Q(x) - x / \zeta(2)$.
-/
noncomputable def R (x : ℝ) : ℝ := Q x - x / (riemannZeta 2).re
/-- **M**

$M(x)$ is the summatory function of the M\"obius function.
-/
noncomputable def M (x : ℝ) : ℤ := ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, moebius n

/-- The function `f(n) = ∑_{d² ∣ n} μ(d)`. -/
noncomputable def sum_sq_div_moebius (n : ℕ) : ℤ :=
    ∑ d ∈ n.divisors.filter (fun d ↦ d ^ 2 ∣ n), (moebius d : ℤ)

/-- If `m, n` are coprime and `a ∣ m`, `b ∣ n`, then `(ab)² ∣ mn` iff `a² ∣ m` and `b² ∣ n`. -/
lemma sq_dvd_mul_iff_of_coprime {m n a b : ℕ} (hmn : m.Coprime n) (ha : a ∣ m) (hb : b ∣ n) :
    (a * b) ^ 2 ∣ m * n ↔ a ^ 2 ∣ m ∧ b ^ 2 ∣ n := by
  admit

/-- The function `sum_sq_div_moebius` is multiplicative (explicitly stated). -/
lemma sum_sq_div_moebius_is_multiplicative_explicit : (sum_sq_div_moebius 1 = 1) ∧
    (∀ m n : ℕ, Nat.Coprime m n →
      sum_sq_div_moebius (m * n) = sum_sq_div_moebius m * sum_sq_div_moebius n) := by
  admit

/- For a prime power `p^k`, `sum_sq_div_moebius` is `1` if `k < 2` and `0` otherwise. -/
lemma sum_sq_div_moebius_prime_pow (p k : ℕ) (hp : Nat.Prime p) :
    sum_sq_div_moebius (p ^ k) = if k < 2 then 1 else 0 := by
  admit

/-- The function `sum_sq_div_moebius` is equal to the indicator function of squarefree numbers. -/
lemma sum_sq_div_moebius_eq_squarefree (n : ℕ) (hn : n > 0) :
    sum_sq_div_moebius n = if Squarefree n then 1 else 0 := by
  admit

/-- **Mobius Lemma 1, initial step**

For any $x>0$, $$Q(x) = \sum_{k\leq x} M\left(\sqrt{\frac{x}{k}}\right)$$.

PROVIDED SOLUTION:
We compute
    $$Q(x) = \sum_{n\leq x} \sum_{d: d^2|n} \mu(d) = \sum_{k, d: k d^2\leq x} \mu(d)$$
    giving the claim.
-/
theorem mobius_lemma_1_sub (x : ℝ) (hx : x > 0) :
    Q x = ∑ k ∈ Ioc 0 ⌊x⌋₊, M (sqrt (x / k)) := by
  admit

/-- The sum `∑' n, μ(n) / n² = 1 / ζ(2)`. -/
theorem sum_moebius_div_sq : ∑' n, (moebius n) / (n : ℝ) ^ 2 = 1 / (riemannZeta 2).re := by
  admit

/-- The integral `∫ u in 0..x, M(√(x/u)) = x · ∑' n, μ(n)/n²`. -/
theorem integral_M_sqrt_div (x : ℝ) (hx : 0 < x) :
    ∫ u in 0..x, (M (sqrt (x / u)) : ℝ) = x * ∑' n : ℕ, (moebius n : ℝ) / (n : ℝ) ^ 2 := by
  admit

/-- **Mobius Lemma 1**

For any $x>0$,
    $$
    R(x) = \sum_{k\leq x} M\left(\sqrt{\frac{x}{k}}\right) -
      \int_0^x M\left(\sqrt{\frac{x}{u}}\right) du.
    $$

PROVIDED SOLUTION:
The equality is immediate from Theorem \ref{mobius-lemma-1-sub} and exchanging the order of
    $\sum$ and $\int$, as is justified by
    $\sum_n |\mu(n)|\int_0^{x/n^2} du \leq \sum_n x/n^2 < \infty$)
    $$\int_0^x M\left(\sqrt{\frac{x}{u}}\right) du = \int_0^x \sum_{n\leq \sqrt{\frac{x}{u}}}
    \mu(n) du = \sum_n \mu(n) \int_0^{\frac{x}{n^2}} du = x \sum_n \frac{\mu(n)}{n^2}
    = \frac{x}{\zeta(2)}.$$
-/
theorem mobius_lemma_1 (x : ℝ) (hx : x > 0) :
    R x = ∑ k ∈ Ioc 0 ⌊x⌋₊, M (sqrt (x / k)) - ∫ u in 0..x, (M (sqrt (x / u)) : ℝ) := by
  admit

/-!
Since our sums start from $1$, the sum $\sum_{k\leq K}$ is empty for $K=0$.
-/
/-- **Mobius Lemma 2 - first step**

For any $K \leq x$,
    $$
    \sum_{k\leq x} M\left(\sqrt{\frac{x}{k}}\right) = \sum_{k\leq K} M\left(\sqrt{\frac{x}{k}}\right)
    + \sum_{K < k\leq x+1} \int_{k-\frac{1}{2}}^{k+\frac{1}{2}}
      M\left(\sqrt{\frac{x}{k}}\right) du.
    $$

PROVIDED SOLUTION:
This is just splitting the sum at $K$.
-/
theorem mobius_lemma_2_sub_1 (x : ℝ) (hx : x > 0) (K : ℕ) (hK : (K : ℝ) ≤ x) :
    ∑ k ∈ Ioc 0 ⌊x⌋₊, M (sqrt (x / k)) = ∑ k ∈ range (K + 1), M (sqrt (x / k)) +
      ∑ k ∈ Ico (K + 1) (⌊x⌋₊ + 2), ∫ _ in (k - 0.5)..(k + 0.5), (M (sqrt (x / k)) : ℝ) := by
  admit

/-- **Mobius Lemma 2 - second step**

For any $K \leq x$, for $f(u) = M(\sqrt{x/u})$,
    $$\sum_{K < k\leq x+1} \int_{k-\frac{1}{2}}^{k+\frac{1}{2}} f(u) du =
      \int_{K+\frac{1}{2}}^{\lfloor x\rfloor + \frac{3}{2}} f(u) du =
      \int_{K+\frac{1}{2}}^x f(u) du,$$

PROVIDED SOLUTION:
This is just splitting the integral at $K$, since $f(u) = M(\sqrt{x/u}) = 0$ for $x>u$.
-/
theorem mobius_lemma_2_sub_2 (x : ℝ) (K : ℕ) (hK : (K : ℝ) ≤ x) :
    let f : ℝ → ℝ := fun u ↦ (M (sqrt (x / u)) : ℝ)
    ∑ k ∈ Ico (K + 1) (⌊x⌋₊ + 2), ∫ u in (k - 0.5)..(k + 0.5), f u =
      ∫ u in (K + 0.5)..(⌊x⌋₊ + 1.5), f u := by
  admit

/-- **Mobius Lemma 2**

For any $x>0$ and any integer $K\geq 0$,
    $$
    \begin{aligned}
    R(x) &= \sum_{k\leq K} M\left(\sqrt{\frac{x}{k}}\right)  -
    \int_0^{K+\frac{1}{2}} M\left(\sqrt{\frac{x}{u}}\right) du \\
    &-\sum_{K < k\leq x+1} \int_{k-\frac{1}{2}}^{k+\frac{1}{2}}
      \left(M\left(\sqrt{\frac{x}{u}}\right) -M\left(\sqrt{\frac{x}{k}}\right)\right) du
    \end{aligned}
    $$

PROVIDED SOLUTION:
We split into two cases. If $K>x$, the second line of (equation eq:singdot) is empty, and the
    first one equals (equation eq:antenor), by $M(t)=0$ for $t<1$, so (equation eq:singdot) holds.

    Now suppose that $K \leq x$. Then we combine Sublemma \ref{mobius-lemma-2-sub-1} and Sublemma
    \ref{mobius-lemma-2-sub-2} with Lemma \ref{mobius-lemma-1} to give the claim.
-/
theorem mobius_lemma_2 (x : ℝ) (hx : x > 0) (K : ℕ) : R x =
    ∑ k ∈ Finset.range (K + 1), M (Real.sqrt (x / k)) -
    (∫ u in 0..(K + 0.5), (M (Real.sqrt (x / u)) : ℝ)) -
    ∑ k ∈ Finset.Ico (K + 1) (⌊x⌋₊ + 2),
      ∫ u in (k - 0.5)..(k + 0.5), (M (Real.sqrt (x / u)) - M (Real.sqrt (x / k)) : ℝ) := by
  admit

end MobiusLemma
