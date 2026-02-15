import Mathlib
import PrimeNumberTheoremAnd.FioriKadiriSwidinskyAristotle
import PrimeNumberTheoremAnd.SecondaryDefinitionsAristotle
import PrimeNumberTheoremAnd.CostaPereiraAristotle
import PrimeNumberTheoremAnd.RosserSchoenfeldPrimeAristotle
import PrimeNumberTheoremAnd.BKLNW_appAristotle
import PrimeNumberTheoremAnd.BKLNW_tablesAristotle
import PrimeNumberTheoremAnd.ButheAristotle
import PrimeNumberTheoremAnd.LogTablesAristotle

/-!
# Tools from BKLNW

In this file we record the results from [reference], excluding Appendix A which is treated elsewhere.  These results convert an initial estimate on $E_\psi(x)$ (provided by Appendix A) to estimates on $E_\theta(x)$.  One first obtains estimates on $E_\theta(x)$ that do not decay in $x$, and then obtain further estimates that decay like $1/\log^k x$ for some $k=1,\dots 5$.
-/

open Chebyshev Finset Real

namespace BKLNW

/-!
## Bounding Etheta uniformly

We first focus on getting bounds on $E_\theta(x)$ that do not decay in $x$.  A key input, provided by Appendix A, is a bound on $E_\psi(x)$ of the form
$$ E_\psi(x) \leq \varepsilon(b) \quad \text{for } x \geq e^b.$$
We also assume a numerical verification $\theta(x) < x$ for $x \leq x_1$ for some $x_1 \geq e^7$.
-/

structure Pre_inputs where
  ε : ℝ → ℝ
  hε : ∀ b ≥ 0, ∀ x ≥ exp b, |ψ x - x| ≤ ε b * x
  x₁ : ℝ
  hx₁ : x₁ ≥ exp 7
  hx₁' : ∀ x ∈ Set.Ioc 0 x₁, θ x < x

lemma Pre_inputs.epsilon_nonneg (I : Pre_inputs) {b : ℝ} (hb : 0 ≤ b) : 0 ≤ I.ε b := by
  admit

/-- **A consequence of Buthe equation (1.7)**

$\theta(x) < x$ for all $1 \leq x \leq 10^{19}$.

PROVIDED SOLUTION:
This follows from Theorem \ref{buthe-theorem-2c}.
-/
theorem buthe_eq_1_7 : ∀ x ∈ Set.Ioc 0 1e19, θ x < x := by
  admit

/-- **Default pre-input parameters**

We take $\varepsilon$ as in Table 8 of [reference], and $x_1 = 10^{19}$.
-/
noncomputable def Pre_inputs.default : Pre_inputs := {
  ε := BKLNW_app.table_8_ε
  hε := BKLNW_app.theorem_2
  x₁ := 1e19
  hx₁ := by admit
  hx₁' := buthe_eq_1_7
}
/-- **BKLNW Lemma 11a**

With the hypotheses as above, we have $\theta(x) \leq (1+\eps(\log x_1)) x)$ for all $x > 0$.

PROVIDED SOLUTION:
Follows immediately from the given hypothesis $\theta(x) \leq \psi(x)$, splitting into the cases $x ≥ x_1$ and $x < x_1$.
-/
theorem lemma_11a (I : Pre_inputs) {x : ℝ} (hx : x > 0) : θ x ≤ (1 + I.ε (log I.x₁)) * x := by
  admit

/-- **BKLNW Lemma 11b**

With the hypotheses as above, we have
  $$ (1 - \eps(b) - c_0(e^{-b/2} + e^{-2b/3} + e^{-4b/5})) x \leq \theta(x)$$
   for all $x \geq e^b$ and $b>0$, where $c_0 = 1.03883$ is the constant from [reference].

PROVIDED SOLUTION:
From Theorem \ref{costa-pereira-theorem-1a} we have $\psi(x) - \theta(x) ≤ \psi(x^{1/2}) + \psi(x^{1/3}) + \psi(x^{1/5})$.  Now apply the hypothesis on $\psi(x)$ and  Theorem \ref{rs-psi-upper}.
-/
theorem lemma_11b (I : Pre_inputs) {b x : ℝ} (hb : 0 < b) (hx : x ≥ exp b) :
    (1 - I.ε b - RS_prime.c₀ * (exp (-b / 2) + exp (-2 * b / 3) + exp (-4 * b / 5))) * x ≤ θ x := by
  admit

/-- **BKLNW Theorem 1a**

For any fixed $X_0 \geq 1$, there exists $m_0 > 0$ such that, for all $x \geq X_0$
  $$ x(1 - m_0) \leq \theta(x). $$
  For any fixed $X_1 \geq 1$, there exists $M_0 > 0$ such that, for all $x \geq X_1$
  $$ \theta(x) \leq x(1 + M_0). $$
  For $X_0, X_1 \geq e^{20}$, we have
  $$ m_0 = \varepsilon(\log X_0) + 1.03883 \left( X_0^{-1/2} + X_0^{-2/3} + X_0^{-4/5} \right) $$
  and
  $$ M_0 = \varepsilon(\log X_1). $$

PROVIDED SOLUTION:
Combine Lemmas \ref{bklnw-lemma-11a} with $b = \log X_1$ for the upper bound, and and \ref{bklnw-lemma-11b} with $b = \log X_0$ for the lower bound.
-/
theorem thm_1a {X₀ X₁ x : ℝ} (hX₀ : X₀ ≥ exp 20) (hX₁ : X₁ ≥ exp 20) (hx₀ : x ≥ X₀) (hx₁ : x ≥ X₁) :
    let m₀ := Pre_inputs.default.ε (log X₀) + RS_prime.c₀ * (X₀^(-1/2:ℝ) + X₀^(-2/3:ℝ) + X₀^(-4/5:ℝ))
    let M₀ := Pre_inputs.default.ε (log X₁)
    x * (1 - m₀) ≤ θ x ∧ θ x ≤ x * (1 + M₀) := by
  admit

/-- One has $x(1-m) \leq \theta(x) \leq x(1+M)$ whenever $x \geq e^b$ and $b,M,m$ obey the condition that $b \geq 20$, $\eps(b) \leq M$, and $\eps(b) + c_0 (e^{-b/2} + e^{-2b/3} + e^{-4b/5}) \leq m$.
-/
theorem thm_1a_crit {b M m : ℝ} (h_check : check_row_prop (b, M, m)) {x : ℝ} (hx : x ≥ exp b) :
    x * (1 - m) ≤ θ x ∧ θ x ≤ x * (1 + M) := by
  admit

/-- The previous theorem holds with $(b,M,m)$ given by the values in [reference].
-/
theorem thm_1a_table {b M m : ℝ} (h_table : (b, M, m) ∈ table_14) {x : ℝ} (hx : x ≥ exp b) :
    x * (1 - m) ≤ θ x ∧ θ x ≤ x * (1 + M) := by
  admit

/-- **BKLNW Corollary 2.1**

$\theta(x) \leq (1 + 1.93378 \times 10^{-8}) x$.

PROVIDED SOLUTION:
We combine together Theorem \ref{from-buthe-eq-1-7} and Theorem \ref{bklnw-thm-1a-table} with $X_1 = 10^{19}$.
-/
theorem cor_2_1 : ∀ x > 0, θ x ≤ (1 + (1.93378e-8*BKLNW_app.table_8_margin)) * x := by
  admit

structure Inputs extends Pre_inputs where
  α : ℝ
  hα : ∀ x > 0, θ x ≤ (1 + α) * x
/-- **Default input parameters**

We take $\alpha = 1.93378 \times 10^{-8}$, so that we have $\theta(x) \leq (1 + \alpha) x$ for all $x$.
-/
noncomputable def Inputs.default : Inputs := {
  toPre_inputs := Pre_inputs.default
  α := 1.93378e-8 * BKLNW_app.table_8_margin
  hα := cor_2_1
}

/-!
## Bounding psi minus theta

In this section we obtain bounds of the shape
$$ \psi(x) - \theta(x) \leq a_1 x^{1/2} + a_2 x^{1/3}$$
for all $x \geq x_0$ and various $a_1, a_2, x_0$.
-/
/-- **BKLNW Equation 2.4**

$$ f(x) := \sum_{k=3}^{\lfloor \log x / \log 2 \rfloor} x^{1/k - 1/3}.$$
-/
noncomputable def f (x : ℝ) : ℝ := ∑ k ∈ Icc 3 ⌊ (log x)/(log 2) ⌋₊, x^(1/k - 1/3 : ℝ)
/-- **BKLNW Proposition 3, substep 1**

Let $x \geq x_0$ and let $\alpha$ be admissible. Then
$$
\frac{\psi(x) - \theta(x) - \theta(x^{1/2})}{x^{1/3}} \leq (1 + \alpha) \sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} x^{\frac{1}{k} - \frac{1}{3}}.
$$

PROVIDED SOLUTION:
Bound each $\theta(x^{1/k})$ term by $(1 + \alpha)x^{1/k}$ in Sublemma \ref{costa-pereira-sublemma-1-1}.
-/
theorem prop_3_sub_1 (I : Inputs) {x₀ x : ℝ} (hx₀ : x₀ ≥ 1)
    (hx : x ≥ x₀) :
    (ψ x - θ x - θ (x^(1/2))) / x^(1/3) ≤ (1 + I.α) * f x := by sorry

/-- **BKLNW Proposition 3, substep 2**

$f$ decreases on $[2^n, 2^{n+1})$.

PROVIDED SOLUTION:
Clear.
-/
theorem prop_3_sub_2 (n : ℕ) (hn : n ≥ 4) : StrictAntiOn f (Set.Ico (2^n) (2^(n + 1))) := by
  admit

noncomputable def u (n : ℕ) : ℝ := ∑ k ∈ Icc 4 n, 2^((n/k:ℝ) - (n/3:ℝ))
/-- **BKLNW Proposition 3, substep 3**

$f(2^n) = 1 + u_n$.

PROVIDED SOLUTION:
Clear.
-/
theorem prop_3_sub_3 (n : ℕ) (hn : n ≥ 3) : f (2^n) = 1 + u n := by
  admit

noncomputable def summand (k n : ℕ) : ℝ :=
  (2 : ℝ) ^ ((n + 1 : ℝ) / k) * ((2 : ℝ) ^ (1 / 3 - 1 / k : ℝ) - 1)

lemma summand_pos.aux {k : ℕ} (hk : 3 < k) : 0 < (2 : ℝ) ^ (1 / 3 - 1 / k : ℝ) - 1 := by
  admit

lemma summand_pos {k : ℕ} (hk : 3 < k) (n : ℕ) : 0 < summand k n := by
  admit

lemma summand_mono {k : ℕ} (hk : 3 < k) : StrictMono (summand k) := by
  admit

lemma sum_gt.aux (k : ℕ) (a b : ℝ) (hk : 3 < k := by decide) (hb1 : 0 ≤ b - 1 := by norm_num only)
    (ha : a ^ k ≤ 1024 := by norm_num only) (hb : b ^ (3 * k) ≤ 2 ^ (k - 3) := by norm_num only) :
    a * (b - 1) ≤ summand k 9 := by
  admit

lemma sum_gt {n : ℕ} (hn : 9 ≤ n) : 2.12 < ∑ k ∈ Icc 4 n, summand k n := by
  admit

lemma u_diff_factored {n : ℕ} (hn : 4 ≤ n) :
    u (n + 1) - u n = 2 ^ (-(n + 1) / 3 : ℝ) * (2 - ∑ k ∈ Icc 4 n, summand k n) := by
  admit

/-- **BKLNW Proposition 3, substep 4**

$u_{n+1} < u_n$ for $n \geq 9$.

PROVIDED SOLUTION:
We have
$$
u_{n+1} - u_n = \sum_{k=4}^{n} 2^{\frac{n+1}{k} - \frac{n+1}{3}}(1 - 2^{\frac{1}{3} - \frac{1}{k}}) + 2^{1 - \frac{n+1}{3}} = 2^{-\frac{n+1}{3}} \left( 2 - \sum_{k=4}^{n} 2^{\frac{n+1}{k}}(2^{\frac{1}{3} - \frac{1}{k}} - 1) \right).
$$
Define $s(k, n) := 2^{\frac{n+1}{k}}(2^{\frac{1}{3} - \frac{1}{k}} - 1)$. Note that $s(k, n)$ is monotone increasing in $n$ for each fixed $k \geq 4$. By numerical computation (using the trick $x \le 2 ^ {p / q} \iff x ^ q \le 2 ^ p$ to verify decimal lower bounds $x$), $\sum_{k=4}^{n} s(k, n) \ge \sum_{k=4}^{9} s(k, 9) > 2.12 > 2$. Thus $u_{n+1} - u_n < 0$.
-/
theorem prop_3_sub_4 (n : ℕ) (hn : 9 ≤ n) : u (n + 1) < u n := by
  admit

/-- **BKLNW Proposition 3, substep 5**

$f(2^n) > f(2^{n+1})$ for $n \geq 9$.

PROVIDED SOLUTION:
This follows from Sublemmas \ref{bklnw-prop-3-sub-3} and \ref{bklnw-prop-3-sub-4}.
-/
theorem prop_3_sub_5 (n : ℕ) (hn : n ≥ 9) : f (2^n) > f (2^(n + 1)) := by
  admit

/-- **BKLNW Proposition 3, substep 6**

$f(x) \leq f(2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})$ on $[2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1}, \infty)$.

PROVIDED SOLUTION:
Follows from Sublemmas \ref{bklnw-prop-3-sub-2} and \ref{bklnw-prop-3-sub-5}.
-/
theorem prop_3_sub_6 (x₀ : ℝ) (hx₀ : x₀ ≥ 2 ^ 9) (x : ℝ)
    (hx : x ≥ 2 ^ (⌊(log x₀) / (log 2)⌋₊ + 1)) :
    f x ≤ f (2 ^ (⌊(log x₀)/(log 2)⌋₊ + 1)) := by
  admit

/-- **BKLNW Proposition 3, substep 7**

$f(x) \leq f(x_0)$ for $x \in [x_0, 2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})$.

PROVIDED SOLUTION:
Follows since $f(x)$ decreases on $[2^{\lfloor \frac{\log x_0}{\log 2} \rfloor}, 2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})$.
-/
theorem prop_3_sub_7 (x₀ : ℝ) (hx₀ : x₀ ≥ 2 ^ 9) (x : ℝ)
    (hx : x ∈ Set.Ico x₀ (2 ^ (⌊(log x₀) / (log 2)⌋₊ + 1))) :
    f x ≤ f x₀ := by
  admit

/-- **BKLNW Proposition 3, substep 8**

$f(x) \leq \max\left(f(x_0), f(2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})\right)$.

PROVIDED SOLUTION:
Combines previous sublemmas.
-/
theorem prop_3_sub_8 (x₀ : ℝ) (hx₀ : x₀ ≥ 2 ^ 9) (x : ℝ)
    (hx : x ≥ x₀) :
    f x ≤ max (f x₀) (f (2 ^ (⌊ (log x₀)/(log 2) ⌋₊ + 1))) := by
  admit

/-- **BKLNW Proposition 3**

Let $x_0 \geq 2^9$. Let $\alpha > 0$ exist such that $\theta(x) \leq (1 + \alpha)x$ for $x > 0$. Then for $x \geq x_0$,
$$
\sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} \theta(x^{1/k}) \leq \eta x^{1/3},
$$
where
$$
\eta = \eta(x_0) = (1 + \alpha) \max\left(f(x_0), f(2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})\right)
$$
with
$$
f(x) := \sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} x^{\frac{1}{k} - \frac{1}{3}}.
$$

PROVIDED SOLUTION:
Combines previous sublemmas.
-/
theorem prop_3 (I : Inputs) {x₀ x : ℝ} (hx₀ : x₀ ≥ 2 ^ 9) (hx : x ≥ x₀) :
    ∑ k ∈ Icc 3 ⌊(log x)/(log 2)⌋₊, θ (x^(1/(k:ℝ))) ≤
      (1 + I.α) * max (f x₀) (f (2^(⌊(log x₀)/(log 2)⌋₊ + 1))) * x^(1/3:ℝ) := by
  admit

/-- **BKLNW Corollary 3.1**

Let $b \geq 7$. Assume $x \geq e^b$. Then we have
$$
\psi(x) - \theta(x) - \theta(x^{1/2}) \leq \eta x^{1/3},
$$
where
$$
\eta = (1 + \alpha) \max\left( f(e^b), f(2^{\lfloor \frac{b}{\log 2} \rfloor + 1}) \right)
$$

PROVIDED SOLUTION:
We apply Proposition \ref{bklnw-prop-3} with $x_0 = e^b$ where we observe that $x_0 = e^b \geq e^7 > 2^9$.
-/
theorem cor_3_1 (I : Inputs) {b x : ℝ} (hb : b ≥ 7) (hx : x ≥ exp b) :
    ψ x - θ x - θ (x^(1/2:ℝ)) ≤
      (1 + I.α) * max (f (exp b)) (f (2^(⌊b / (log 2)⌋ + 1))) * x^(1/3:ℝ) := by
  admit

/-- **BKLNW Proposition 4, part a**

If $7 \leq b \leq 2\log x_1$, then we have
$$
\theta(x^{1/2}) \leq (1 + \varepsilon(\log x_1))x^{1/2} \quad \text{for } x \geq e^b.
$$

PROVIDED SOLUTION:
Note that in the paper, the inequality in Proposition 4 is strict, but the
argument can only show nonstrict inequalities.
If $e^b \leq x \leq x_1^2$, then $x^{1/2} \leq x_1$, and thus
$$
\theta(x^{1/2}) < x^{1/2} \quad \text{for } e^b \leq x \leq x_1^2.
$$
On the other hand, if $x^{1/2} > x_1 = e^{\log x_1}$, then we have by (2.7)
$$
\theta(x^{1/2}) \leq \psi(x^{1/2}) \leq (1 + \varepsilon(\log x_1))x^{1/2},
$$
since $\log x_1 \geq 7$. The last two inequalities for $\theta(x^{1/2})$ combine to establish (2.8).
-/
theorem prop_4_a (I : Inputs) {b x : ℝ} (hx : exp b ≤ x) :
    θ (x ^ (1 / 2 : ℝ)) ≤ (1 + I.ε (log I.x₁)) * x ^ (1 / 2 : ℝ) := by
  admit

/-- **BKLNW Proposition 4, part b**

If $b > 2\log x_1$, then we have
$$
\theta(x^{1/2}) \leq (1 + \varepsilon(b/2))x^{1/2} \quad \text{for } x \geq e^b.
$$

PROVIDED SOLUTION:
Note that in the paper, the inequality in Proposition 4 is strict, but the
argument can only show nonstrict inequalities. As in the above subcase, we have for $x \geq e^b$
$$
\theta(x^{1/2}) \leq \psi(x^{1/2}) \leq (1 + \varepsilon(b/2))x^{1/2},
$$
since $x^{1/2} > e^{b/2} > x_1 \geq e^7$.
-/
theorem prop_4_b (I : Inputs) {b x : ℝ} (hb : 7 ≤ b) (hx : exp b ≤ x) :
    θ (x ^ (1 / 2 : ℝ)) ≤ (1 + I.ε (b / 2)) * x ^ (1 / 2 : ℝ) := by
  admit

/-- **Definition of a1**

$a_1$ is equal to $1 + \varepsilon(\log x_1)$ if $b \leq 2\log x_1$, and equal to $1 + \varepsilon(b/2)$ if $b > 2\log x_1$.
-/
noncomputable def Inputs.a₁ (I : Inputs) (b : ℝ) : ℝ :=
  if b ≤ 2 * log I.x₁ then 1 + I.ε (log I.x₁)
  else 1 + I.ε (b / 2)
/-- **Definition of a2**

$a_2$ is defined by
$$
a_2 = (1 + \alpha) \max\left( f(e^b), f(2^{\lfloor \frac{b}{\log 2} \rfloor + 1}) \right).
$$
-/
noncomputable def Inputs.a₂ (I : Inputs) (b : ℝ) : ℝ :=
  (1 + I.α) * (max (f (exp b)) (f (2^(⌊ b / (log 2) ⌋₊ + 1))))
/-- **BKLNW Theorem 5**

Let $\alpha > 0$ exist such that
$$
\theta(x) \leq (1 + \alpha)x \quad \text{for all } x > 0.
$$
Assume for every $b \geq 7$ there exists a positive constant $\varepsilon(b)$ such that
$$
\psi(x) - x \leq \varepsilon(b)x \quad \text{for all } x \geq e^b.
$$
Assume there exists $x_1 \geq e^7$ such that
$$
\theta(x) < x \quad \text{for } x \leq x_1.
$$
Let $b \geq 7$. Then, for all $x \geq e^b$ we have
$$
\psi(x) - \theta(x) < a_1 x^{1/2} + a_2 x^{1/3},
$$
where
$$
a_1 = \begin{cases}
1 + \varepsilon(\log x_1) & \text{if } b \leq 2\log x_1, \\
1 + \varepsilon(b/2) & \text{if } b > 2\log x_1,
\end{cases}
$$
and
$$
a_2 = (1 + \alpha) \max\left( f(e^b), f(2^{\lfloor \frac{b}{\log 2} \rfloor + 1}) \right).
$$

PROVIDED SOLUTION:
We have $\psi(x) - \theta(x) = \theta(x^{1/2}) + \sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} \theta(x^{1/k})$. For any $b \geq 7$, setting $x_0 = e^b$ in Proposition 4, we bound $\sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} \theta(x^{1/k})$ by $\eta x^{1/3}$ as defined in (2.3). We bound $\theta(x^{1/2})$ with Proposition \ref{bklnw-prop-4} by taking either $a_1 = 1 + \varepsilon(\log x_1)$ for $b \leq 2\log x_1$ or $a_1 = 1 + \varepsilon(b/2)$ for $b > 2\log x_1$.
-/
theorem thm_5 (I : Inputs) {b x : ℝ} (hb : b ≥ 7) (hx : x ≥ exp b) :
    ψ x - θ x ≤ I.a₁ b * x^(1/2:ℝ) + I.a₂ b * x^(1/3:ℝ) := by
  admit

noncomputable def a₁ : ℝ → ℝ := Inputs.default.a₁

noncomputable def a₂ : ℝ → ℝ := Inputs.default.a₂
/-- **BKLNW Corollary 5.1**

Let $b \geq 7$. Then for all $x \geq e^b$ we have $\psi(x) - \vartheta(x) < a_1 x^{1/2} + a_2 x^{1/3}$, where $a_1 = a_1(b) = 1 + 1.93378 \times 10^{-8}$ if $b \leq 38 \log 10$, $1 + \varepsilon(b/2)$ if $b > 38 \log 10$, and $a_2 = a_2(b) = (1 + 1.93378 \times 10^{-8}) \max\left( f(e^b), f(2^{\lfloor \frac{b}{\log 2} \rfloor + 1}) \right)$, where $f$ is defined by (2.4) and values for $\varepsilon(b/2)$ are from Table 8.

PROVIDED SOLUTION:
This is Theorem 5 applied to the default inputs in Definition \ref{bklnw-inputs}.
-/
theorem cor_5_1 {b x : ℝ} (hb : b ≥ 7) (hx : x ≥ exp b) :
    ψ x - θ x ≤ a₁ b * x ^ (1 / 2 : ℝ) + a₂ b * x ^ (1 / 3 : ℝ) := by
  admit

def table_cor_5_1 : List (ℝ × ℝ × ℕ) :=
  [(20, 1.4262, 4)
  , (25, 1.2195, 4)
  , (30, 1.1210, 4)
  , (35, 1.07086, 5)
  , (40, 1.04319, 5)
  , (43, 1.03252, 5)
  , (100, 1 + 2.420e-4, 7)
  , (150, 1 + 3.748e-6, 8)
  , (200, 1 + 7.713e-8, 9)
  , (250, 1 + 2.025e-8, 9)
  , (300, 1 + 1.937e-8, 8)
 ]

-- cor_5_1_rem is proved sorry-free in BKLNW_a2_bounds.lean (as BKLNW.cor_5_1_rem)
-- via LeanCert certified interval arithmetic for all 11 table entries.



/-!
## Bounding theta(x)-x with a logarithmic decay, I: large x

In this section and the next ones we obtain bounds of the shape
$$ x \left(1 - \frac{m_k}{\log^k x}\right) \leq \theta(x)$$
for all $x \geq X_0$ and
$$ \theta(x) \leq x \left(1 + \frac{M_k}{\log^k x}\right)$$
for all $x \geq X_1$, for various $k, m_k, M_k, X_0, X_1$, with $k \in \{1,\dots,5\}$.

For this section we focus on estimates that are useful when $x$ is extremely large, e.g., $x \geq e^{25000}$.
-/

/-
Show that the function g in the proof of the following lemma is decreasing
-/
lemma g_decreasing_interval (A C : ℝ) (hA : 0 < A) (hC : 0 < C) (u v : ℝ) (hu : 4 * A ^ 2 / C ^ 2 ≤ u) (huv : u ≤ v) :
    v ^ A * Real.exp (-C * Real.sqrt v) ≤ u ^ A * Real.exp (-C * Real.sqrt u) := by
  admit

/-- **BKLNW Lemma 6**

Suppose there exists $c_1, c_2, c_3, c_4 > 0$ such that
$$
|\theta(x) - x| \leq c_1 x (\log x)^{c_2} \exp(-c_3 (\log x)^{\frac{1}{2}}) \quad \text{for all } x \geq c_4.
$$
Let $k > 0$ and let $b \geq \max\left(\log c_4, \log\left(\frac{4(c_2 + k)^2}{c_3^2}\right)\right)$. Then for all $x \geq e^b$ we have
$$
|\theta(x) - x| \leq \frac{\mathcal{A}_k(b) x}{(\log x)^k},
$$
where
$$
\mathcal{A}_k(b) = c_1 \cdot b^{c_2 + k} e^{-c_3\sqrt{b}}.
$$

PROVIDED SOLUTION:
We denote $g(x) = (\log x)^{c_2 + k} \exp(-c_3 (\log x)^{\frac{1}{2}})$. By (equation bklnw_3.3), $|\theta(x) - x| < \frac{c_1 g(x) x}{(\log x)^k}$ for all $x \geq c_4$. It suffices to bound $g$: by calculus, $g(x)$ decreases when $x \geq \frac{4(c_2 + k)^2}{c_3^2}$. Therefore $|\theta(x) - x| \leq \frac{c_1 g(e^b) x}{(\log x)^k}$. Note that $c_1 g(e^b) = \mathcal{A}_k(b)$ and the condition on $b$ follows from the conditions $e^b \geq c_4$ and $e^b \geq \frac{4(c_2 + k)^2}{c_3^2}$.
-/
theorem lem_6 {c₁ c₂ c₃ c₄ k b x : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hc₄ : 0 < c₄)
    (hθ : Eθ.classicalBound c₁ c₂ c₃ 1 c₄)
    (hk : 0 < k)
    (hb : b ≥ max (log c₄) (((4 * (c₂ + k) ^ 2) / (c₃ ^ 2))))
    (hx : x ≥ exp b) :
    let A := c₁ * b ^ (c₂ + k) * exp (-c₃ * sqrt b)
    Eθ x ≤ A / (log x) ^ k := by
  admit

/-- **BKLNW Corollary 14.1**

Suppose one has an asymptotic bound $E_\psi$ with parameters $A,B,C,R,e^{x_0}$ (which need to satisfy some additional bounds) with $x_0 \geq 1000$.  Then $E_\theta$ obeys an asymptotic bound with parameters $A', B, C, R, e^{x_0}$, where
  $$ A' := A (1 + \frac{1}{A} (\frac{R}{x_0})^B \exp(C \sqrt{\frac{x_0}{R}}) (a_1(x_0) \exp(\frac{-x_0}{2}) + a_2(x_0) \exp(\frac{-2 x_0}{3}))) $$
  and $a_1(x_0), a_2(x_0)$ are as in Corollary \ref{bklnw-cor-5-1}.

PROVIDED SOLUTION:
We write $\theta(x) - x = \psi(x) - x + \theta(x) - \psi(x)$, apply the triangle inequality, and invoke Corollary \ref{bklnw-cor-5-1} to obtain
$$
E_\theta(x) \leq A (\frac{\log x}{R})^B \exp(-C (\frac{\log x}{R})^{\frac{1}{2}}) + a_1(x_0) x^{-\frac{1}{2}} + a_2(x_0) x^{-\frac{2}{3}}$$
$$ \leq A (\frac{\log x}{R})^B \exp(-C (\frac{\log x}{R})^{\frac{1}{2}}) (1 + \frac{a_1(x_0) \exp(C \sqrt{\frac{\log x}{R}})}{A \sqrt{x} (\frac{\log x}{R})^B} + \frac{a_2(x_0) \exp(C \sqrt{\frac{\log x}{R}})}{A x^{\frac{2}{3}} (\frac{\log x}{R})^B}).$$
The function in brackets decreases for $x \geq e^{x_0}$ with $x_0 \geq 1000$ (assuming reasonable hypotheses on $A,B,C,R$) and thus we obtain the desired bound with $A'$ as above.
-/
theorem cor_14_1 {A B C R x₀ : ℝ} (hB : B > 0) (hC : C ∈ Set.Ioc 0 (sqrt (R * x₀))) (hR : R ∈ Set.Icc 1 10)
    (hx₀ : x₀ ≥ 1000)
    (hEψ : Eψ.classicalBound A B C R (exp x₀)) :
    let A' := (A + (R / x₀) ^ B * exp (C * sqrt (x₀ / R)) *
      (a₁ x₀ * exp (-x₀ / 2) + a₂ x₀ * exp (-2 * x₀ / 3)))
    Eθ.classicalBound A' B C R (exp x₀) := by
  admit

/-!
## Bounding theta(x)-x with a logarithmic decay, II: medium x

In this section we tackle medium $x$.

TODO: formalize Lemma 8 and Corollary 8.1
-/

/-!
## Bounding theta(x)-x with a logarithmic decay, III: small x

In this section we tackle small $x$.

TODO: formalize (3.17), (3.18), Lemma 9, Corollary 9.1
-/


/-!
## Bounding theta(x)-x with a logarithmic decay, IV: very small x

In this section we tackle very small $x$.

TODO: Formalize Lemma 10
-/


/-!
## Final bound on Etheta(x)

Now we put everything together.

TODO: Section 3.7.1; 3.7.2; 3.7.3; 3.7.4
-/


noncomputable def Table_15 : List (ℝ × (Fin 5 → ℝ)) := [
  (0, ![1.2323e0, 3.9649e0, 2.0829e1, 1.5123e2, 1.3441e5]),
  (log 1e5, ![5.5316e-2, 6.4673e-1, 7.5612e0, 8.9346e1, 1.3441e5]),
  (log 5e5, ![2.6724e-2, 3.5744e-1, 4.7808e0, 6.3944e1, 1.3441e5]),
  (log 1e6, ![2.3240e-2, 3.2309e-1, 4.4916e0, 6.2444e1, 1.3441e5]),
  (log 5e6, ![1.0236e-2, 1.5952e-1, 2.4860e0, 5.7184e1, 1.3441e5]),
  (log 1e7, ![8.4725e-3, 1.3675e-1, 2.2071e0, 5.7184e1, 1.3441e5]),
  (log 5e7, ![3.8550e-3, 6.8701e-2, 1.2244e0, 5.7184e1, 1.3441e5]),
  (log 1e8, ![2.7457e-3, 5.0612e-2, 9.4259e-1, 5.7184e1, 1.3441e5]),
  (log 1e9, ![9.5913e-4, 2.0087e-2, 4.2065e-1, 5.7184e1, 1.3441e5]),
  (log 1e10, ![3.7787e-4, 8.7526e-3, 2.0274e-1, 5.7184e1, 1.3441e5]),
  (log 19035709163, ![2.6773e-4, 6.3370e-3, 1.5000e-1, 5.7184e1, 1.3441e5]),
  (log 2e10, ![2.4601e-4, 5.8365e-3, 1.3848e-1, 5.7184e1, 1.3441e5]),
  (log 5e10, ![1.8556e-4, 4.5722e-3, 1.1266e-1, 5.7184e1, 1.3441e5]),
  (log 1e11, ![1.3392e-4, 3.4053e-3, 8.6589e-2, 5.7184e1, 1.3441e5]),
  (log 2e11, ![7.8683e-5, 2.0591e-3, 5.3886e-2, 5.7184e1, 1.3441e5]),
  (log 3e11, ![7.0193e-5, 1.8758e-3, 5.0536e-2, 5.7184e1, 1.3441e5]),
  (log 4e11, ![7.0193e-5, 1.8758e-3, 5.0536e-2, 5.7184e1, 1.3441e5]),
  (log 5e11, ![6.9322e-5, 1.8717e-3, 5.0536e-2, 5.7184e1, 1.3441e5]),
  (log 6e11, ![6.9322e-5, 1.8717e-3, 5.0536e-2, 5.7184e1, 1.3441e5]),
  (28, ![4.3555e-5, 1.2196e-3, 3.4148e-2, 5.7184e1, 1.3441e5]),
  (29, ![2.7336e-5, 7.9272e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (30, ![1.7139e-5, 5.1415e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (31, ![1.0735e-5, 3.3277e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (32, ![7.0053e-6, 2.2417e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (33, ![4.3798e-6, 1.4454e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (34, ![2.7360e-6, 9.3023e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (35, ![1.7078e-6, 5.9771e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (36, ![1.0652e-6, 3.8345e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (37, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (38, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (39, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (40, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (41, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (42, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (43, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (19 * log 10, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (44, ![7.8163e-7, 3.5174e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (45, ![5.0646e-7, 2.3298e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (46, ![3.2935e-7, 1.5480e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (47, ![2.1308e-7, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (48, ![1.3791e-7, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (49, ![8.9140e-8, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (50, ![5.7545e-8, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (55, ![6.3417e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (60, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (65, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (70, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (80, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (90, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (100, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (200, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (300, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (400, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (500, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (600, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (700, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (800, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (900, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (1000, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (1500, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (2000, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (2500, ![2.2885e-9, 5.7783e-6, 1.4591e-2, 3.6840e1, 9.3021e4]),
  (3000, ![1.3915e-10, 4.2091e-7, 1.2733e-3, 3.8516e0, 1.1651e4]),
  (3500, ![8.7646e-12, 3.0896e-8, 1.0891e-4, 3.8390e-1, 1.3533e3]),
  (4000, ![5.7410e-13, 2.3108e-9, 9.3007e-6, 3.7436e-2, 1.5068e2]),
  (5000, ![2.8715e-15, 1.4645e-11, 7.4687e-8, 3.8091e-4, 1.9426e0]),
  (6000, ![1.7952e-17, 1.0951e-13, 6.6798e-10, 4.0747e-6, 2.4856e-2]),
  (7000, ![1.4744e-19, 1.0468e-15, 7.4322e-12, 5.2769e-8, 3.7466e-4]),
  (8000, ![1.6007e-21, 1.2966e-17, 1.0502e-13, 8.5065e-10, 6.8903e-6]),
  (9000, ![2.2253e-23, 2.0250e-19, 1.8428e-15, 1.6769e-11, 1.5260e-7]),
  (10000, ![3.8228e-25, 3.8610e-21, 3.8997e-17, 3.9387e-13, 3.9780e-9]),
  (11000, ![7.9284e-27, 8.8005e-23, 9.7685e-19, 1.0844e-14, 1.2036e-10]),
  (12000, ![1.9331e-28, 2.3390e-24, 2.8302e-20, 3.4245e-16, 4.1437e-12]),
  (13000, ![5.5830e-30, 7.5371e-26, 1.0175e-21, 1.3737e-17, 1.8544e-13]),
  (14000, ![1.8399e-31, 2.7598e-27, 4.1396e-23, 6.2094e-19, 9.3141e-15]),
  (15000, ![6.5712e-33, 1.0514e-28, 1.6823e-24, 2.6916e-20, 4.3065e-16]),
  (16000, ![2.5739e-34, 4.3756e-30, 7.4384e-26, 1.2646e-21, 2.1497e-17]),
  (17000, ![1.1168e-35, 2.0101e-31, 3.6182e-27, 6.5127e-23, 1.1723e-18]),
  (18000, ![5.3739e-37, 1.0211e-32, 1.9400e-28, 3.6860e-24, 7.0033e-20]),
  (19000, ![2.7357e-38, 5.4714e-34, 1.0943e-29, 2.1886e-25, 4.3772e-21]),
  (20000, ![1.5041e-39, 3.1585e-35, 6.6329e-31, 1.3929e-26, 2.9251e-22]),
  (21000, ![9.0606e-41, 1.9934e-36, 4.3853e-32, 9.6477e-28, 2.1225e-23]),
  (22000, ![5.6101e-42, 1.2904e-37, 2.9678e-33, 6.8258e-29, 1.5700e-24]),
  (23000, ![3.7554e-43, 9.0129e-39, 2.1631e-34, 5.1915e-30, 1.2460e-25]),
  (24000, ![2.6756e-44, 6.6889e-40, 1.6723e-35, 4.1806e-31, 1.0452e-26]),
  (25000, ![7.5635e-45, 1.8909e-40, 4.7272e-36, 1.1818e-31, 2.9545e-27])
]

/- [FIX]: This fixes a typo in the original paper https://arxiv.org/pdf/2002.11068. -/
/-- **Theorem 1b**

Let $k$ be an integer with $1 \leq k \leq 5$. For any fixed $X_0 > 1$, there exists $m_k > 0$ such that, for all $x \geq X_0$
  $$ x(1 - \frac{m_k}{(\log x)^k}) \leq \theta(x). $$
  For any fixed $X_1 > 1$, there exists $M_k > 0$ such that, for all $x \geq X_1$
  $$ \theta(x) \leq x(1 + \frac{M_k}{(\log x)^k}). $$
  In the case $k = 0$ and $X_0, X_1 \geq e^{20}$, we have
  $$ m_0 = \varepsilon(\log X_0) + 1.03883 \left( X_0^{-1/2} + X_0^{-2/3} + X_0^{-4/5} \right) $$
  and
  $$ M_0 = \varepsilon(\log X_1). $$
-/
theorem thm_1b (k : ℕ) (hk : k ≤ 5) {X₀ X₁ x : ℝ} (hX₀ : X₀ > 1) (hX₁ : X₁ > 1) (hx₀ : x ≥ X₀)
    (hx₁ : x ≥ X₁) : ∃ mₖ Mₖ, (x * (1 - mₖ / (log x)^k) ≤ θ x) ∧ (θ x ≤ x * (1 + Mₖ / (log x)^k)) := by
  sorry


/- [FIX]: This fixes a typo in the original paper https://arxiv.org/pdf/2002.11068. -/
/-- **BKLNW Theorem 1b, table form**

See [reference] for values of $m_k$ and $M_k$, for $k \in \{1,2,3,4,5\}$.
-/
theorem thm_1b_table {X₀ : ℝ} (hX₀ : X₀ > 1) {M : Fin 5 → ℝ} (h : (X₀, M) ∈ Table_15) (k : Fin 5) {x : ℝ} (hx : x ≥ X₀) :
  x * (1 - M k / (log x)^(k.val + 1)) ≤ θ x ∧ θ x ≤ x * (1 + M k / (log x)^(k.val + 1)) :=
  by sorry



/-!
## Computational examples

Now we apply the previous theorem.

TODO: Corollary 11.1, 11.2
-/


end BKLNW
