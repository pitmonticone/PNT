import Mathlib
import PrimeNumberTheoremAnd.SecondarySummaryAristotle

namespace Lcm

open ArithmeticFunction hiding log
open Finset Nat Real

/-!
# The least common multiple sequence is not highly abundant for large \(n\)
-/

/-!
## Problem statement and notation
-/
/-- $\sigma(n)$ is the sum of the divisors of $n$.
-/
def σ : ArithmeticFunction ℕ := sigma 1

noncomputable abbrev σnorm (n : ℕ) : ℝ := (σ n : ℝ) / (n : ℝ)
/-- A positive integer \(N\) is called \emph{highly abundant} (HA) if
  $$
    \sigma(N) > \sigma(m)
  $$
  for all positive integers \(m < N\), where \(\sigma(n)\) denotes the sum of the positive divisors
  of \(n\).
-/
def HighlyAbundant (N : ℕ) : Prop :=
  ∀ m : ℕ, m < N → σ m < σ N

/-!
Informally, a highly abundant number has an unusually large sum of divisors.
-/
/-- For each integer \(n \ge 1\), define
  $$
    L_n := \mathrm{lcm}(1,2,\dots,n).
  $$
  We call \((L_n)_{n \ge 1}\) the \emph{least common multiple sequence}.
-/
def L (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm _root_.id

/-!
Clearly $L_n$ has a lot of divisors, and numerical experiments for small $n$ suggests that $L_n$
is often highly abundant.  This leads to the following question:
-/


/-!
\begin{quote}
\textbf{Original MathOverflow question.}
Is it true that every value in the sequence \(L_n = \mathrm{lcm}(1,2,\dots,n)\) is highly abundant?
Equivalently,
$$
  \{L_n : n \ge 1\} \subseteq HA?
$$
\end{quote}

Somewhat surprisingly, the answer is \emph{no}: not every \(L_n\) is highly abundant.

It has previously been verified in Lean that \(L_n\) is highly aboundant for $n \leq 70$,
$81 \leq n \leq 96$, $125 \leq n \leq 148$, $169 \leq n \leq 172$, and not highly abondant for all
other $n ≤ 10^{10}$.  The arguments here establish the non-highly-abundance of \(L_n\) for all
$n \geq 89683^2$ sufficiently large \(n\), thus completing the determination in Lean of all $n$ for
which \(L_n\) is highly abundant. This argument was taken from
\href{https://mathoverflow.net/questions/501066/is-the-least-common-multiple-sequence-textlcm1-2-dots-n-a-subset-of-t?noredirect=1\#comment1313839_501066}{this
MathOverflow answer}.

\subsection{A general criterion using three medium primes and three large primes}
-/

/-!
The key step in the proof is to show that, if one can find six primes $p_1,p_2,p_3,q_1,q_2,q_3$
obeying a certain inequality, then one can find a competitor $M < L_n$ to $L_n$ with
$\sigma(M) > \sigma(L_n)$, which will demonstrate that $L_n$ is not highly abundant.
More precisely:
-/
/-- In the next few subsections we assume that $n \geq 1$ and that \(p_1,p_2,p_3,q_1,q_2,q_3\) are
  primes satisfiying
  $$
    \sqrt{n} < p_1 < p_2 < p_3 < q_1 < q_2 < q_3 < n
  $$
  and the key criterion
  $$
    \prod_{i=1}^3\Bigl(1+\frac{1}{q_i}\Bigr)
    \le
    \Biggl( \prod_{i=1}^3 \Bigl(1+\frac{1}{p_i(p_i+1)}\Bigr) \Biggr)
    \Bigl(1 + \frac{3}{8n}\Bigr)
    \Biggl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Biggr).
  $$

  NOTE: In the Lean formalization of this argument, we index the primes from 0 to 2 rather than
  from 1 to 3.
-/
structure Criterion where
  n : ℕ
  hn : n ≥ 1
  p : Fin 3 → ℕ
  hp : ∀ i, Nat.Prime (p i)
  hp_mono : StrictMono p
  q : Fin 3 → ℕ
  hq : ∀ i, Nat.Prime (q i)
  hq_mono : StrictMono q
  h_ord_1 : √(n : ℝ) < p 0
  h_ord_2 : p 2 < q 0
  h_ord_3 : q 2 < n
  h_crit : ∏ i, (1 + (1 : ℝ) / q i) ≤
    (∏ i, (1 + (1 : ℝ) / (p i * (p i + 1)))) * (1 + (3 : ℝ) / (8 * n)) *
      (1 - 4 * (∏ i, (p i : ℝ)) / ∏ i, (q i : ℝ))
/-- We have $4 p_1 p_2 p_3 < q_1 q_2 q_3$.

PROVIDED SOLUTION:
Obvious from the non-negativity of the left-hand side of (equation eq:main-ineq).
-/
theorem Criterion.prod_p_le_prod_q (c : Criterion) : 4 * ∏ i, c.p i < ∏ i, c.q i := by
  admit

lemma Criterion.p_gt_two (c : Criterion) (i : Fin 3) : 2 < c.p i := by
  admit

lemma Criterion.q_gt_two (c : Criterion) (i : Fin 3) : 2 < c.q i := by
  admit

/-!
## Factorisation of \(L_n\) and construction of a competitor
-/

noncomputable def Criterion.L' (c : Criterion) : ℕ := L c.n / ∏ i, c.q i

lemma Criterion.prod_q_dvd_L (c : Criterion) : ∏ i, c.q i ∣ L c.n := by
  admit

lemma Criterion.L_pos (c : Criterion) : 0 < L c.n := by
  admit

lemma Criterion.L'_pos (c : Criterion) : 0 < c.L' := by
  admit

lemma Criterion.L_eq_prod_q_mul_L' (c : Criterion) : L c.n = (∏ i, c.q i) * c.L' := by
  admit

lemma Criterion.val_two_L' (c : Criterion) : (c.L').factorization 2 = Nat.log 2 c.n := by
  admit

lemma Criterion.val_p_L' (c : Criterion) (i : Fin 3) : (c.L').factorization (c.p i) = 1 := by
  admit

/-- **Factorisation of \\(L_n\\)**

There exists a positive integer \(L'\) such that
  $$
    L_n = q_1 q_2 q_3 \, L'
  $$
  and each prime \(q_i\) divides \(L_n\) exactly once and does not divide \(L'\).

PROVIDED SOLUTION:
Since \(q_i < n\), the prime \(q_i\) divides \(L_n\) exactly once (as \(q_i^2 > n\)).
  Hence we may write \(L_n = q_1 q_2 q_3 L'\) where \(L'\) is the quotient obtained by removing
  these prime factors.  By construction, \(q_i \nmid L'\) for each \(i\).
-/
theorem Criterion.ln_eq (c : Criterion) : L c.n = c.q 0 * c.q 1 * c.q 2 * c.L' := by
  admit

/-- **Factorisation of \\(L_n\\)**

There exists a positive integer \(L'\) such that
  $$
    L_n = q_1 q_2 q_3 \, L'
  $$
  and each prime \(q_i\) divides \(L_n\) exactly once and does not divide \(L'\).

PROVIDED SOLUTION:
Since \(q_i < n\), the prime \(q_i\) divides \(L_n\) exactly once (as \(q_i^2 > n\)).
  Hence we may write \(L_n = q_1 q_2 q_3 L'\) where \(L'\) is the quotient obtained by removing
  these prime factors.  By construction, \(q_i \nmid L'\) for each \(i\).
-/
theorem Criterion.q_not_dvd_L' (c : Criterion) : ∀ i, ¬(c.q i ∣ c.L') := by
  admit

/-- **Normalised divisor sum for \\(L_n\\)**

Let \(L'\) be as in Lemma~`lemma_Lprime-def`. Then
  $$
    \frac{\sigma(L_n)}{L_n}
    \;=\;
    \frac{\sigma(L')}{L'} \prod_{i=1}^3 \Bigl(1 + \frac{1}{q_i}\Bigr).
  $$

PROVIDED SOLUTION:
Use the multiplicativity of \(\sigma(\cdot)\) and the fact that each \(q_i\) occurs to the first
  power in \(L_n\).  Then
  $$
    \sigma(L_n)
    = \sigma(L') \prod_{i=1}^3 \sigma(q_i)
    = \sigma(L') \prod_{i=1}^3 (1+q_i).
  $$
  Dividing by \(L_n = L' \prod_{i=1}^3 q_i\) gives
  $$
    \frac{\sigma(L_n)}{L_n}
    = \frac{\sigma(L')}{L'} \prod_{i=1}^3 \frac{1+q_i}{q_i}
    = \frac{\sigma(L')}{L'} \prod_{i=1}^3 \Bigl(1 + \frac{1}{q_i}\Bigr).
  $$
-/
theorem Criterion.σnorm_ln_eq (c : Criterion) :
    σnorm (L c.n) = σnorm c.L' * ∏ i, (1 + (1 : ℝ) / c.q i) := by
  admit

def Criterion.m (c : Criterion) : ℕ := (∏ i, c.q i) / (4 * ∏ i, c.p i)

def Criterion.r (c : Criterion) : ℕ := (∏ i, c.q i) % (4 * ∏ i, c.p i)
/-- There exist integers \(m \ge 0\) and \(r\) satisfying \(0 < r < 4 p_1 p_2 p_3\) and
   $$q_1 q_2 q_3 = 4 p_1 p_2 p_3 m + r $$

PROVIDED SOLUTION:
This is division with remainder.
-/
theorem Criterion.r_ge (c : Criterion) : 0 < c.r := by
  admit

/-- There exist integers \(m \ge 0\) and \(r\) satisfying \(0 < r < 4 p_1 p_2 p_3\) and
  $$
    q_1 q_2 q_3 = 4 p_1 p_2 p_3 m + r
  $$

PROVIDED SOLUTION:
This is division with remainder.
-/
theorem Criterion.r_le (c : Criterion) : c.r < 4 * ∏ i, c.p i := by
  admit

/-- There exist integers \(m \ge 0\) and \(r\) satisfying \(0 < r < 4 p_1 p_2 p_3\) and
  $$
    q_1 q_2 q_3 = 4 p_1 p_2 p_3 m + r
  $$

PROVIDED SOLUTION:
This is division with remainder.
-/
theorem Criterion.prod_q_eq (c : Criterion) : ∏ i, c.q i = (4 * ∏ i, c.p i) * c.m + c.r := by
  admit

/-- With $m,r$ as above, define the competitor
  $$
    M := 4 p_1 p_2 p_3 m L'.
  $$
-/
noncomputable def Criterion.M (c : Criterion) : ℕ := (4 * ∏ i, c.p i) * c.m * c.L'

lemma Criterion.m_pos (c : Criterion) : 0 < c.m := by
  admit

lemma Criterion.M_pos (c : Criterion) : 0 < c.M := by
  admit

lemma Criterion.val_two_M_ge_L' (c : Criterion) : (c.M).factorization 2 ≥ (c.L').factorization 2 + 2
    := by
  admit

lemma Criterion.val_p_M_ge_two (c : Criterion) (i : Fin 3) : (c.M).factorization (c.p i) ≥ 2 := by
  admit

/-- **Basic properties of \\(M\\)**

With notation as above, we have:
  \begin{enumerate}
    \item \(M < L_n\).
    \item
    $$
      1 < \frac{L_n}{M} = \Bigl(1 - \frac{r}{q_1 q_2 q_3}\Bigr)^{-1}
        < \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)^{-1}.
    $$
  \end{enumerate}

PROVIDED SOLUTION:
The first item is by construction of the division algorithm.
  For the second, note that
  $$
    L_n = q_1 q_2 q_3 L' = (4 p_1 p_2 p_3 m + r) L' > 4 p_1 p_2 p_3 m L' = M,
  $$
  since \(r>0\). For the third,
  $$
    \frac{L_n}{M} = \frac{4 p_1 p_2 p_3 m + r}{4 p_1 p_2 p_3 m}
                = 1 + \frac{r}{4 p_1 p_2 p_3 m}
                = \Bigl(1 - \frac{r}{4 p_1 p_2 p_3 m + r}\Bigr)^{-1}
                = \Bigl(1 - \frac{r}{q_1 q_2 q_3}\Bigr)^{-1}.
  $$
  Since \(0 < r < 4p_1p_2p_3\) and \(4p_1p_2p_3 < q_1q_2q_3\), we have
  $$
    0<\frac{r}{q_1 q_2 q_3}<\frac{4p_1p_2p_3}{q_1 q_2 q_3},
  $$
  so
  $$
    \Bigl(1-\frac{r}{q_1 q_2 q_3}\Bigr)^{-1}
    < \Bigl(1-\frac{4p_1p_2p_3}{q_1 q_2 q_3}\Bigr)^{-1}.
  $$
-/
theorem Criterion.M_lt (c : Criterion) : c.M < L c.n := by
  admit

/-- **Basic properties of \\(M\\)**

With notation as above, we have:
  \begin{enumerate}
    \item \(M < L_n\).
    \item
    $$
      1 < \frac{L_n}{M} = \Bigl(1 - \frac{r}{q_1 q_2 q_3}\Bigr)^{-1}
        < \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)^{-1}.
    $$
  \end{enumerate}

PROVIDED SOLUTION:
The first item is by construction of the division algorithm.
  For the second, note that
  $$
    L_n = q_1 q_2 q_3 L' = (4 p_1 p_2 p_3 m + r) L' > 4 p_1 p_2 p_3 m L' = M,
  $$
  since \(r>0\). For the third,
  $$
    \frac{L_n}{M} = \frac{4 p_1 p_2 p_3 m + r}{4 p_1 p_2 p_3 m}
                = 1 + \frac{r}{4 p_1 p_2 p_3 m}
                = \Bigl(1 - \frac{r}{4 p_1 p_2 p_3 m + r}\Bigr)^{-1}
                = \Bigl(1 - \frac{r}{q_1 q_2 q_3}\Bigr)^{-1}.
  $$
  Since \(0 < r < 4p_1p_2p_3\) and \(4p_1p_2p_3 < q_1q_2q_3\), we have
  $$
    0<\frac{r}{q_1 q_2 q_3}<\frac{4p_1p_2p_3}{q_1 q_2 q_3},
  $$
  so
  $$
    \Bigl(1-\frac{r}{q_1 q_2 q_3}\Bigr)^{-1}
    < \Bigl(1-\frac{4p_1p_2p_3}{q_1 q_2 q_3}\Bigr)^{-1}.
  $$
-/
theorem Criterion.Ln_div_M_gt (c : Criterion) : (1 : ℝ) < L c.n / c.M := by
  admit

/-- **Basic properties of \\(M\\)**

With notation as above, we have:
  \begin{enumerate}
    \item \(M < L_n\).
    \item
    $$
      1 < \frac{L_n}{M} = \Bigl(1 - \frac{r}{q_1 q_2 q_3}\Bigr)^{-1}
        < \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)^{-1}.
    $$
  \end{enumerate}

PROVIDED SOLUTION:
The first item is by construction of the division algorithm.
  For the second, note that
  $$
    L_n = q_1 q_2 q_3 L' = (4 p_1 p_2 p_3 m + r) L' > 4 p_1 p_2 p_3 m L' = M,
  $$
  since \(r>0\). For the third,
  $$
    \frac{L_n}{M} = \frac{4 p_1 p_2 p_3 m + r}{4 p_1 p_2 p_3 m}
                = 1 + \frac{r}{4 p_1 p_2 p_3 m}
                = \Bigl(1 - \frac{r}{4 p_1 p_2 p_3 m + r}\Bigr)^{-1}
                = \Bigl(1 - \frac{r}{q_1 q_2 q_3}\Bigr)^{-1}.
  $$
  Since \(0 < r < 4p_1p_2p_3\) and \(4p_1p_2p_3 < q_1q_2q_3\), we have
  $$
    0<\frac{r}{q_1 q_2 q_3}<\frac{4p_1p_2p_3}{q_1 q_2 q_3},
  $$
  so
  $$
    \Bigl(1-\frac{r}{q_1 q_2 q_3}\Bigr)^{-1}
    < \Bigl(1-\frac{4p_1p_2p_3}{q_1 q_2 q_3}\Bigr)^{-1}.
  $$
-/
theorem Criterion.Ln_div_M_lt (c : Criterion) :
    L c.n / c.M < (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i))⁻¹ := by
  admit

/-!
## A sufficient condition

We give a sufficient condition for $\sigma(M) \geq \sigma(L_n)$.
-/
/-- **A sufficient inequality**

Suppose
  $$
    \frac{\sigma(M)}{M}
    \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)
    \;\ge\; \frac{\sigma(L_n)}{L_n}.
  $$
  Then \(\sigma(M) \ge \sigma(L_n)\), and so \(L_n\) is not highly abundant.

PROVIDED SOLUTION:
By Lemma~`lemma_M-basic`,
  $$
    \frac{L_n}{M} < \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)^{-1}.
  $$
  Hence
  $$
    \frac{\sigma(M)}{M} \ge \frac{\sigma(L_n)}{L_n}
    \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)^{-1}
    > \frac{\sigma(L_n)}{L_n} \cdot \frac{M}{L_n}.
  $$
  Multiplying both sides by \(M\) gives
  $$
    \sigma(M) > \sigma(L_n) \cdot \frac{M}{L_n}
  $$
  and hence
  $$
    \sigma(M) \ge \sigma(L_n),
  $$
  since \(M/L_n<1\) and both sides are integers.
-/
theorem Criterion.not_highlyAbundant_1 (c : Criterion)
    (h : σnorm c.M * (1 - (4 : ℝ) * (∏ i, c.p i) / (∏ i, c.q i)) ≥ σnorm (L c.n)) :
    ¬HighlyAbundant (L c.n) := by
  admit

/-!
Combining Lemma `lemma_criterion-sufficient` with Lemma `lemma_sigmaLn`, we see that it
suffices to bound \(\sigma(M)/M\) from below in terms of \(\sigma(L')/L'\):
-/
/-- **Reduction to a lower bound for \\(\\sigma(M)/M\\)**

If
  $$
    \frac{\sigma(M)}{M}
    \;\ge\;
    \frac{\sigma(L')}{L'}
    \Biggl( \prod_{i=1}^3 \Bigl(1+\frac{1}{p_i(p_i+1)}\Bigr) \Biggr)
    \Bigl(1 + \frac{3}{8n}\Bigr),
  $$
  then $L_n$ is not highly abundant.

PROVIDED SOLUTION:
Insert (equation eq:sigmaM-lower) and (equation eq:sigmaLn) into the desired inequality and compare
  with the assumed bound (equation eq:main-ineq); this is a straightforward rearrangement.
-/
theorem Criterion.not_highlyAbundant_2 (c : Criterion)
    (h : σnorm c.M ≥ σnorm c.L' * (∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) *
    (1 + (3 : ℝ) / (8 * c.n))) : ¬HighlyAbundant (L c.n) := by
  admit

/-!
## Conclusion of the criterion
-/

private lemma σnorm_ratio_ge_aux {k : ℕ} (n : ℕ) (hk : 2 ^ k ≤ n) :
    (∑ i ∈ Finset.range (k + 3), (1 / 2 : ℝ) ^ i) / (∑ i ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ i) ≥
      1 + 3 / (8 * n) := by
  admit

/-- **Lower bound for \\(\\sigma(M)/M\\)**

With notation as above,
  $$
    \frac{\sigma(M)}{M}
    \ge
    \frac{\sigma(L')}{L'}
    \Biggl( \prod_{i=1}^3 \Bigl(1 + \frac{1}{p_i(p_i+1)}\Bigr) \Biggr)
    \Bigl(1 + \frac{3}{8n}\Bigr).
  $$

PROVIDED SOLUTION:
By multiplicativity, we have
  $$
    \frac{\sigma(M)}{M}
    = \frac{\sigma(L')}{L'}
    \prod_p \frac{1+p^{-1}+\dots+p^{-\nu_p(M)}}{1+p^{-1}+\dots+p^{-\nu_p(L')}}.
  $$
  The contribution of $p=p_i$ is
  $$
    \frac{(1+p_i^{-1}+p_i^{-2})}{1+p^{-1}_i}
    = 1 + \frac{1}{p_i(p_i+1)}.
  $$
  The contribution of $p=2$ is
  $$
    \frac{1+2^{-1}+\dots+2^{-k-2}}{1+2^{-1}+\dots+2^{-k}},
  $$
  where \(k\) is the largest integer such that \(2^k \le n\).
  A direct calculation yields
  $$
    \frac{(1+2^{-1}+\dots+2^{-k-2})}{1+2^{-1}+\dots+2^{-k}}
    = \frac{2^{k+3}-1}{2^{k+3}-4}
    = 1 + \frac{3}{2^{k+3}-4},
  $$
  Finally, since \(2^k \le n < 2^{k+1}\), we have \(2^{k+3} < 8n\), so
  $$
    \frac{3}{2^{k+3}-4} \ge \frac{3}{8n},
  $$
  So the contribution from the prime \(2\) is at least \(1 + 3/(8n)\).

  Finally, the contribution of all other primes is at least \(1\).
-/
theorem Criterion.σnorm_M_ge_σnorm_L'_mul (c : Criterion) :
    σnorm c.M ≥
      σnorm c.L' * (∏ i, (1 + 1 / (c.p i * (c.p i + 1 : ℝ)))) * (1 + 3 / (8 * c.n)) := by
  admit

/-!
We have thus completed the key step of demonstrating a sufficient criterion to establish that
$L_n$ is not highly abundant:
-/
/-- Let $n \geq 1$.
  Suppose that primes \(p_1,p_2,p_3,q_1,q_2,q_3\) satisfy
  $$
    \sqrt{n} < p_1 < p_2 < p_3 < q_1 < q_2 < q_3 < n
  $$
  and the key criterion (equation eq:main-ineq).
  Then \(L_n\) is not highly abundant.

PROVIDED SOLUTION:
By Lemma~`lemma_sigmaM-lower-final`, the condition (equation eq:sigmaM-lower) holds.
  By Lemma~`lemma_criterion-reduced` this implies
  $$
    \frac{\sigma(M)}{M}
    \Bigl(1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}\Bigr)
    \ge \frac{\sigma(L_n)}{L_n}.
  $$
  Applying Lemma~`lemma_criterion-sufficient`, we obtain \(\sigma(M) \ge \sigma(L_n)\) with
  \(M < L_n\), so \(L_n\) cannot be highly abundant.
-/
theorem Criterion.not_highlyAbundant (c : Criterion) : ¬HighlyAbundant (L c.n) := by
  admit

/-!
**Remark:** Analogous arguments allow other pairs \((c,\alpha)\) in place of \((4,3/8)\),
such as \((2,1/4)\), \((6,17/36)\), \((30,0.632\dots)\); or even \((1,0)\) provided more primes are
used on the \(p\)-side than the \(q\)-side to restore an asymptotic advantage.
-/

abbrev X₀ := 89693

lemma hsqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) : √(n : ℝ) ≥ 89693 := by
  admit

lemma log_X₀_gt : Real.log X₀ > 11.4 := by
  admit

lemma hlog {n : ℕ} (hn : n ≥ X₀ ^ 2) : log √(n : ℝ) ≥ 11.4 := by
  admit

lemma hε_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) : 0 < 1 + 1 / (log √(n : ℝ)) ^ 3 := by
  admit

lemma log_X₀_pos : 0 < Real.log X₀ := by
  admit

/-!
## Choice of six primes \(p_i,q_i\) for large \(n\)
-/

/-!
To finish the proof we need to locate six primes $p_1,p_2,p_3,q_1,q_2,q_3$ obeying the required
inequality.  Here we will rely on the prime number theorem of Dusart [reference].
-/
/-- **Choice of medium primes \\(p_i\\)**

Let \(n \ge X_0^2\). Set \(x := \sqrt{n}\). Then there exist primes \(p_1,p_2,p_3\) with
  $$
    p_i \le x \Bigl(1 + \frac{1}{\log^3 x}\Bigr)^i
  $$
  and \(p_1 < p_2 < p_3\).
  Moreover, \(\sqrt{n} < p_1\)

PROVIDED SOLUTION:
Apply Proposition~\ref{Dusart_prop_5_4} successively with
  \(x, x(1+1/\log^3 x), x(1+1/\log^3 x)^2\), keeping track of the resulting primes and bounds.
  For \(n\) large and \(x = \sqrt{n}\), we have \(\sqrt{n} < p_1\) as soon as the first interval
  lies strictly above \(\sqrt{n}\); this can be enforced by taking \(n\) large enough.
-/
theorem exists_p_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ p : Fin 3 → ℕ, (∀ i, Nat.Prime (p i)) ∧ StrictMono p ∧
      (∀ i, p i ≤ √(n : ℝ) * (1 + 1 / (log √(n : ℝ)) ^ 3) ^ (i + 1 : ℝ)) ∧
      √(n : ℝ) < p 0 := by
  admit

/-- **Choice of large primes \\(q_i\\)**

Let \(n \ge X_0^2\). Then there exist primes \(q_1 < q_2 < q_3\) with
  $$
    q_{4-i} \ge n \Bigl(1 + \frac{1}{\log^3 \sqrt{n}}\Bigr)^{-i}
  $$
  for \(i = 1,2,3\), and \(q_1 < q_2 < q_3 < n\).

PROVIDED SOLUTION:
Apply Theorem~\ref{Dusart_prop_5_4} with suitable values of \(x\) slightly below \(n\),
  e.g.\ \(x = n(1+1/\log^3\sqrt{n})^{-i}\), again keeping track of the intervals.  For \(n\) large
  enough, these intervals lie in \((\sqrt{n},n)\) and contain primes \(q_i\) with the desired
  ordering.
-/
theorem exists_q_primes {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∃ q : Fin 3 → ℕ, (∀ i, Nat.Prime (q i)) ∧ StrictMono q ∧
      (∀ i : Fin 3, n * (1 + 1 / (log √(n : ℝ)) ^ 3) ^ (-((3 : ℝ) - (i : ℕ))) ≤ q i) ∧
      q 2 < n := by
  admit

/-!
## Bounding the factors in \eqref{eq:main-ineq

}
-/
/-- **Bounds for the \\(q_i\\)-product**

With \(p_i,q_i\) as in Lemmas~`lemma_choose-pi` and `lemma_choose-qi`, we have
  $$
    \prod_{i=1}^3 \Bigl(1 + \frac{1}{q_i}\Bigr)
    \le
    \prod_{i=1}^3 \Bigl(1 + \frac{\bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^i}{n} \Bigr).
  $$

PROVIDED SOLUTION:
By Lemma~`lemma_choose-qi`, each \(q_i\) is at least
  $$
    n\Bigl(1 + \frac{1}{\log^3 \sqrt{n}}\Bigr)^{-j}
  $$
  for suitable indices \(j\), so \(1/q_i\) is bounded above by
  $$
    \frac{\bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^i}{n}
  $$
  after reindexing. Multiplying the three inequalities gives (equation eq:qi-upper).
-/
theorem prod_q_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∏ i, (1 + (1 : ℝ) / (exists_q_primes hn).choose i) ≤
      ∏ i : Fin 3, (1 + (1 + 1 / (log √(n : ℝ)) ^ 3) ^ ((i : ℕ) + 1 : ℝ) / n) := by
  admit

/-- **Bounds for the \\(p_i\\)-product**

With \(p_i\) as in Lemma~`lemma_choose-pi`, we have for large \(n\)
  $$
    \prod_{i=1}^3 \Bigl(1 + \frac{1}{p_i(p_i+1)}\Bigr)
    \ge
    \prod_{i=1}^3
    \Bigl(
      1 + \frac{1}{\bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^{2i} (n + \sqrt{n})}
    \Bigr).
  $$

PROVIDED SOLUTION:
By Lemma~`lemma_choose-pi`, \(p_i \le \sqrt{n} (1+1/\log^3\sqrt{n})^i\).  Hence
  $$
    p_i^2 \le n\bigl(1 + \tfrac{1}{\log^3 \sqrt{n}}\bigr)^{2i}
  \quad\text{and}\quad
    p_i+1 \le p_i(1 + 1/\sqrt{n}) \le (1+1/\sqrt{n}) p_i.
  $$
  From these one gets
  $$
    p_i(p_i+1) \le \bigl(1 + \tfrac{1}{\log^3 \sqrt{n}}\bigr)^{2i} (n + \sqrt{n}),
  $$
  and hence
  $$
    \frac{1}{p_i(p_i+1)} \ge
    \frac{1}{\bigl(1 + \tfrac{1}{\log^3 \sqrt{n}}\bigr)^{2i} (n + \sqrt{n})}.
  $$
  Taking \(1+\cdot\) and multiplying over \(i=1,2,3\) gives (equation eq:pi-lower).
-/
theorem prod_p_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    ∏ i, (1 + (1 : ℝ) /
        ((exists_p_primes hn).choose i * ((exists_p_primes hn).choose i + 1))) ≥
      ∏ i : Fin 3,
        (1 + 1 / ((1 + 1 / (log √(n : ℝ)) ^ 3) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n))) := by
  admit

/-- **Lower bound for the product ratio \\(p_i/q_i\\)**

With \(p_i,q_i\) as in Lemmas~`lemma_choose-pi` and `lemma_choose-qi`, we have
  $$
    1 - \frac{4 p_1 p_2 p_3}{q_1 q_2 q_3}
    \ge
    1 - \frac{4 \bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^{12}}{n^{3/2}}.
  $$

PROVIDED SOLUTION:
We have \(p_i \le \sqrt{n} (1+1/\log^3 \sqrt{n})^i\), so
  $$
    p_1 p_2 p_3 \le n^{3/2} \bigl(1 + \tfrac{1}{\log^3 \sqrt{n}}\bigr)^{6}.
  $$
  Similarly, \(q_i \ge n(1+1/\log^3 \sqrt{n})^{-i}\), so
  $$
    q_1 q_2 q_3 \ge n^3 \bigl(1 + \tfrac{1}{\log^3 \sqrt{n}}\bigr)^{-6}.
  $$
  Combining,
  $$
    \frac{p_1 p_2 p_3}{q_1 q_2 q_3} \le
    \frac{n^{3/2} \bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^{6}}{n^3
    \bigl(1 + \frac{1}{\log^3\sqrt{n}}\bigr)^{-6}}
    = \frac{\bigl(1 + \frac{1}{\log^3 \sqrt{n}}\bigr)^{12}}{n^{3/2}}.
  $$
  This implies (equation eq:pq-ratio).
-/
theorem pq_ratio_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 - ((4 : ℝ) * ∏ i, ((exists_p_primes hn).choose i : ℝ))
    / ∏ i, ((exists_q_primes hn).choose i : ℝ) ≥
    1 - 4 * (1 + 1 / (log √(n : ℝ)) ^ 3) ^ 12 / n ^ (3 / 2 : ℝ) := by
  admit

/-!
## Reduction to a small epsilon-inequality
-/
/-- **Uniform bounds for large \\(n\\)**

For all \(n \ge X_0^2 = 89693^2\) we have
  $$
    \frac{1}{\log^3 \sqrt{n}}
    \le 0.000675,
    \qquad
    \frac{1}{n^{3/2}} \le \frac{1}{89693}\cdot\frac{1}{n}.
  $$
  and
  $$ \frac{1}{n+\sqrt{n}} \ge \frac{1}{1 + 1/89693}\cdot\frac{1}{n}. $$

PROVIDED SOLUTION:
This is a straightforward calculus and monotonicity check: the left-hand sides are
  decreasing in \(n\) for \(n \ge X_0^2\), and equality (or the claimed upper bound) holds at
  \(n=X_0^2\).  One can verify numerically or symbolically.
-/
theorem inv_cube_log_sqrt_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 / (log √(n : ℝ)) ^ 3 ≤ 0.000675 := by
  admit

/-- **Uniform bounds for large \\(n\\)**

For all \(n \ge X_0^2 = 89693^2\) we have
  $$
    \frac{1}{\log^3 \sqrt{n}}
    \le 0.000675,
    \qquad
    \frac{1}{n^{3/2}} \le \frac{1}{89693}\cdot\frac{1}{n}.
  $$
  and
  $$ \frac{1}{n+\sqrt{n}} \ge \frac{1}{1 + 1/89693}\cdot\frac{1}{n}. $$

PROVIDED SOLUTION:
This is a straightforward calculus and monotonicity check: the left-hand sides are
  decreasing in \(n\) for \(n \ge X_0^2\), and equality (or the claimed upper bound) holds at
  \(n=X_0^2\).  One can verify numerically or symbolically.
-/
theorem inv_n_pow_3_div_2_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 / ((n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (89693 : ℝ)) * (1 / (n : ℝ)) := by
  admit

/-- **Uniform bounds for large \\(n\\)**

For all \(n \ge X_0^2 = 89693^2\) we have
  $$
    \frac{1}{\log^3 \sqrt{n}}
    \le 0.000675,
    \qquad
    \frac{1}{n^{3/2}} \le \frac{1}{89693}\cdot\frac{1}{n}.
  $$
  and
  $$ \frac{1}{n+\sqrt{n}} \ge \frac{1}{1 + 1/89693}\cdot\frac{1}{n}. $$

PROVIDED SOLUTION:
This is a straightforward calculus and monotonicity check: the left-hand sides are
  decreasing in \(n\) for \(n \ge X_0^2\), and equality (or the claimed upper bound) holds at
  \(n=X_0^2\).  One can verify numerically or symbolically.
-/
theorem inv_n_add_sqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 / (n + √(n : ℝ)) ≥ (1 / (1 + 1 / (89693 : ℝ))) * (1 / (n : ℝ)) := by
  admit

/-- **Polynomial approximation of the inequality**

For \(0 \le \varepsilon \le 1/89693^2\), we have
  $$
    \prod_{i=1}^3 (1 + 1.000675^i \varepsilon)
    \le
    \Bigl(1 + 3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3\Bigr),
  $$
  and
  $$
    \prod_{i=1}^3 \Bigl(1 + \frac{\varepsilon}{1.000675^{2i}}\frac{1}{1 + 1/89693}\Bigr)
    \Bigl(1 + \frac{3}{8}\varepsilon\Bigr)
    \Bigl(1 - \frac{4 \times 1.000675^{12}}{89693}\varepsilon\Bigr)
    \ge
    1 + 3.36683\varepsilon - 0.01\varepsilon^2.
  $$

PROVIDED SOLUTION:
Expand each finite product as a polynomial in \(\varepsilon\), estimate the coefficients using
  the bounds in Lemma~`lemma_eps-bounds`, and bound the tails by simple inequalities such as
  $$
    (1+C\varepsilon)^k \le 1 + k C\varepsilon + \dots
  $$
  for small \(\varepsilon\).
  All coefficients can be bounded numerically in a rigorous way; this step is a finite computation
  that can be checked mechanically.
-/
theorem prod_epsilon_le {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (89693 ^ 2 : ℝ)) :
    ∏ i : Fin 3, (1 + (1.000675 : ℝ) ^ ((i : ℕ) + 1 : ℝ) * ε) ≤
      1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 := by
  admit

/-- **Polynomial approximation of the inequality**

For \(0 \le \varepsilon \le 1/89693^2\), we have
  $$
    \prod_{i=1}^3 (1 + 1.000675^i \varepsilon)
    \le
    \Bigl(1 + 3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3\Bigr),
  $$
  and
  $$
    \prod_{i=1}^3 \Bigl(1 + \frac{\varepsilon}{1.000675^{2i} (1 + \frac{1}{89693})}\Bigr)
    \Bigl(1 + \frac{3}{8}\varepsilon\Bigr)
    \Bigl(1 - \frac{4 \times 1.000675^{12}}{89693}\varepsilon\Bigr)
    \ge
    1 + 3.36683\varepsilon - 0.01\varepsilon^2.
  $$

PROVIDED SOLUTION:
Expand each finite product as a polynomial in \(\varepsilon\), estimate the coefficients using
  the bounds in Lemma~`lemma_eps-bounds`, and bound the tails by simple inequalities such as
  $$
    (1+C\varepsilon)^k \le 1 + k C\varepsilon + \dots
  $$
  for small \(\varepsilon\).
  All coefficients can be bounded numerically in a rigorous way; this step is a finite computation
  that can be checked mechanically.
-/
theorem prod_epsilon_ge {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (89693 ^ 2 : ℝ)) :
    (∏ i : Fin 3,
      (1 + ε / ((1.000675 : ℝ) ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1/89693)))) *
        (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * (1.000675 : ℝ) ^ 12 / 89693 * ε) ≥
      1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
  admit

/-- **Final polynomial comparison**

For \(0 \le \varepsilon \le 1/89693^2\), we have
  $$
    1 + 3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3
    \le 1 + 3.36683\varepsilon - 0.01\varepsilon^2.
  $$

PROVIDED SOLUTION:
This is equivalent to
  $$
    3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3
    \le 3.36683\varepsilon - 0.01\varepsilon^2,
  $$
  or
  $$
    0 \le (3.36683 - 3.01)\varepsilon - (3.01+0.01)\varepsilon^2 - 1.01\varepsilon^3.
  $$
  Factor out \(\varepsilon\) and use that \(0<\varepsilon \le 1/89693^2\) to check that the
  resulting quadratic in \(\varepsilon\) is nonnegative on this interval.  Again, this is a
  finite computation that can be verified mechanically.
-/
theorem final_comparison {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (89693 ^ 2 : ℝ)) :
    1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤ 1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
  admit

/-- **Verification of \\eqref{eq:main-ineq} for large \\(n\\)**

For every integer \(n \ge X_0^2 = 89693^2 \approx 8.04\times 10^9\), the
  primes \(p_i,q_i\) constructed in Lemmas~`lemma_choose-pi` and `lemma_choose-qi` satisfy the
  inequality (equation eq:main-ineq).

PROVIDED SOLUTION:
Combine Lemma~`lemma_qi-product`, Lemma~`lemma_pi-product`, and
  Lemma~`lemma_pq-ratio`.  Then apply Lemma~`lemma_eps-bounds` and set \(\varepsilon = 1/n\).
  The products are bounded by the expressions in Lemma~`lemma_poly-ineq`, and the inequality in
  Lemma~`lemma_final-comparison` then ensures that (equation eq:main-ineq) holds.
-/
noncomputable def Criterion.mk' {n : ℕ} (hn : n ≥ X₀ ^ 2) : Criterion where
  n := n
  p := (exists_p_primes hn).choose
  q := (exists_q_primes hn).choose
  hn := le_trans (by admit) hn
  hp := (exists_p_primes hn).choose_spec.1
  hp_mono := (exists_p_primes hn).choose_spec.2.1
  hq := (exists_q_primes hn).choose_spec.1
  hq_mono := (exists_q_primes hn).choose_spec.2.1
  h_ord_1 := (exists_p_primes hn).choose_spec.2.2.2
  h_ord_2 := by admit

  h_ord_3 := (exists_q_primes hn).choose_spec.2.2.2
  h_crit := by admit

/-!
## Conclusion for large \(n\)
-/
/-- **Non-highly abundant for large \\(n\\)**

For every integer \(n \ge 89693^2\), the integer \(L_n\) is not highly
  abundant.

PROVIDED SOLUTION:
By Proposition~`proposition_ineq-holds-large-n`, there exist primes
  \(p_1,p_2,p_3,q_1,q_2,q_3\) satisfying the hypotheses of Theorem~\ref{thm:criterion}.
  Hence \(L_n\) is not highly abundant.
-/
theorem L_not_HA_of_ge (n : ℕ) (hn : n ≥ 89693 ^ 2) : ¬HighlyAbundant (L n) := by
  admit

/-!
## Bonus material

The following result is not needed for this application, but is worth recording nevertheless.
-/
/-- **Formula for log of L equals Chebyshev psi**

For every $n$, $\log L_n = \sum_{p \leq n} \lfloor \log n / \log p \rfloor \log p$.

PROVIDED SOLUTION:
Compute the number of times $p$ divides $L_n$ and use the fundamental theorem of arithmetic.
-/
theorem L_eq_prod (n : ℕ) :
    L n = ∏ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
      p ^ ⌊Real.log n / Real.log p⌋₊ := by sorry

/-- **Formula for Chebyshev psi**

For every $n$, $\psi(n) = \sum_{p \leq n} \lfloor \log n / \log p \rfloor \log p$, where $\psi$ is the Chebyshev psi function.

PROVIDED SOLUTION:
Compute the number of times $p$ divides $L_n$ and use the fundamental theorem of arithmetic.
-/
theorem psi_eq_prod (n : ℕ) :
    Chebyshev.psi n = ∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
      ⌊Real.log n / Real.log p⌋₊ * Real.log p := by sorry

/-- **Log of L equals Chebyshev psi**

For every $n$, $\log L_n = \psi(n)$, where $\psi$ is the Chebyshev psi function.

PROVIDED SOLUTION:
Combine the previous results.
-/
theorem log_L_eq_psi (n : ℕ) : Real.log (L n) = Chebyshev.psi n := by sorry



end Lcm
