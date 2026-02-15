import Mathlib
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.BasicAristotle
import PrimeNumberTheoremAnd.DefsAristotle
import PrimeNumberTheoremAnd.WienerAristotle

set_option lang.lemmaCmd true

open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

lemma Set.Ico_subset_Ico_of_Icc_subset_Icc {a b c d : ℝ} (h : Set.Icc a b ⊆ Set.Icc c d) :
    Set.Ico a b ⊆ Set.Ico c d := by
  admit

lemma th43_b (x : ℝ) (hx : 2 ≤ x) :
    Nat.primeCounting ⌊x⌋₊ =
      θ x / log x + ∫ t in Set.Icc 2 x, θ t / (t * (Real.log t) ^ 2) := by
  admit

/-- **finsum-range-eq-sum-range**

For any arithmetic function $f$ and real number $x$, one has
  $$ \sum_{n \leq x} f(n) = \sum_{n \leq ⌊x⌋_+} f(n)$$
  and
  $$ \sum_{n < x} f(n) = \sum_{n < ⌈x⌉_+} f(n).$$

PROVIDED SOLUTION:
Straightforward.
-/
lemma finsum_range_eq_sum_range {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R} (x : ℝ) :
    ∑ᶠ (n : ℕ) (_: n < x), f n = ∑ n ∈ range ⌈x⌉₊, f n := by
  admit

lemma finsum_range_eq_sum_range' {R : Type*} [AddCommMonoid R] {f : ArithmeticFunction R}
    (x : ℝ) : ∑ᶠ (n : ℕ) (_ : n ≤ x), f n = ∑ n ∈ Iic ⌊x⌋₊, f n := by
  admit

lemma log2_pos : 0 < log 2 := by
  admit

/-- If u ~ v and w-u = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (w - u) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  admit

/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  admit

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  admit

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
  admit

/-- `√x · log x = o(x)` as `x → ∞`. -/
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  admit

/-- `(⌊x⌋₊ + 1) / x → 1` as `x → ∞`. -/
lemma tendsto_floor_add_one_div_self : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ + 1 : ℝ) / x) atTop (nhds 1) := by
  admit

/-- `x =Θ x / c` for nonzero constant `c`. -/
lemma isTheta_self_div_const {c : ℝ} (hc : c ≠ 0) : (fun x : ℝ ↦ x) =Θ[atTop] fun x ↦ x / c := by
  admit

/-- Filtered sum over `Iic n` equals filtered sum over `Icc 1 n` for primes. -/
lemma filter_prime_Iic_eq_Icc (n : ℕ) : filter Prime (Iic n) = filter Prime (Icc 1 n) := by
  admit

/-- `Icc 0 n = insert 0 (Icc 1 n)` -/
lemma Icc_zero_eq_insert (n : ℕ) : Icc 0 n = insert 0 (Icc 1 n) := by
  admit

/-- **chebyshev-asymptotic**

One has
  $$ \sum_{p \leq x} \log p = x + o(x).$$

PROVIDED SOLUTION:
From the prime number theorem we already have
  $$ \sum_{n \leq x} \Lambda(n) = x + o(x)$$
  so it suffices to show that
  $$ \sum_{j \geq 2} \sum_{p^j \leq x} \log p = o(x).$$
  Only the terms with $j \leq \log x / \log 2$ contribute, and each $j$ contributes at most
  $\sqrt{x} \log x$ to the sum, so the left-hand side is $O( \sqrt{x} \log^2 x ) = o(x)$ as
  required.
-/
theorem chebyshev_asymptotic : θ ~[atTop] id := by
  admit

theorem chebyshev_asymptotic_finsum :
    (fun x ↦ ∑ᶠ (p : ℕ) (_ : p ≤ x) (_ : Nat.Prime p), log p) ~[atTop] fun x ↦ x := by
  admit

theorem chebyshev_asymptotic' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun t ↦ ε * t)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ (x : ℝ), θ x = x + f x := by
  admit

theorem chebyshev_asymptotic'' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun _ ↦ ε)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ x > (0 : ℝ), θ x = x + x * (f x) := by
  admit

-- one could also consider adding a version with p < x instead of p \leq x
/-- **primorial-bounds**

We have
    $$ \prod_{p \leq x} p = \exp( x + o(x) )$$

PROVIDED SOLUTION:
Exponentiate Theorem \ref{chebyshev_asymptotic}.
-/
theorem primorial_bounds :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
      ∀ x : ℝ, ∏ p ∈ (Iic ⌊x⌋₊).filter Nat.Prime, p = exp (x + E x) := by
  admit

theorem primorial_bounds_finprod :
    ∃ E : ℝ → ℝ, E =o[atTop] (fun x ↦ x) ∧
      ∀ x : ℝ, ∏ᶠ (p : ℕ) (_ : p ≤ x) (_ : Nat.Prime p), p = exp (x + E x) := by
  admit

lemma continuousOn_log0 :
    ContinuousOn (fun x ↦ -1 / (x * log x ^ 2)) {0, 1, -1}ᶜ := by
  admit

lemma continuousOn_log1 : ContinuousOn (fun x ↦ (log x ^ 2)⁻¹ * x⁻¹) {0, 1, -1}ᶜ := by
  admit

lemma integral_log_inv (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in a..b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in a..b, ((log t)^2)⁻¹ := by
  admit

lemma integral_log_inv' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  admit

lemma integral_log_inv'' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    (log a)⁻¹ * a + ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) + ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  admit

lemma integral_log_inv_pos (x : ℝ) (hx : 2 < x) :
    0 < ∫ t in Set.Icc 2 x, (log t)⁻¹ := by
  admit

lemma integral_log_inv_ne_zero (x : ℝ) (hx : 2 < x) :
    ∫ t in Set.Icc 2 x, (log t)⁻¹ ≠ 0 := by
  admit

lemma pi_asymp_aux (x : ℝ) (hx : 2 ≤ x) : Nat.primeCounting ⌊x⌋₊ =
    (log x)⁻¹ * θ x + ∫ t in Set.Icc 2 x, θ t * (t * log t ^ 2)⁻¹ := by
  admit

theorem pi_asymp'' :
    (fun x => ((Nat.primeCounting ⌊x⌋₊ : ℝ) / ∫ t in Set.Icc 2 x, 1 / log t) - (1 : ℝ)) =o[atTop]
      fun _ => (1 : ℝ) := by
  admit

/-- **pi-asymp**

There exists a function $c(x)$ such that $c(x) = o(1)$ as $x \to \infty$ and
  $$ \pi(x) = (1 + c(x)) \int_2^x \frac{dt}{\log t}$$
  for all $x$ large enough.

PROVIDED SOLUTION:
We have the identity
  $$ \pi(x) = \frac{1}{\log x} \sum_{p \leq x} \log p
  + \int_2^x (\sum_{p \leq t} \log p) \frac{dt}{t \log^2 t}$$
  as can be proven by interchanging the sum and integral and using the fundamental theorem of
  calculus.  For any $\eps$, we know from Theorem \ref{chebyshev_asymptotic} that there is $x_\eps$
  such that $\sum_{p \leq t} \log p = t + O(\eps t)$ for $t \geq x_\eps$, hence for $x \geq x_\eps$
  $$ \pi(x) = \frac{1}{\log x} (x + O(\eps x))
  + \int_{x_\eps}^x (t + O(\eps t)) \frac{dt}{t \log^2 t} + O_\eps(1)$$
  where the $O_\eps(1)$ term can depend on $x_\eps$ but is independent of $x$.  One can evaluate
  this after an integration by parts as
  $$ \pi(x) = (1+O(\eps)) \int_{x_\eps}^x \frac{dt}{\log t} + O_\eps(1)$$
  $$  = (1+O(\eps)) \int_{2}^x \frac{dt}{\log t} $$
  for $x$ large enough, giving the claim.
-/
theorem pi_asymp :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ (x : ℝ) in atTop,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * ∫ t in (2 : ℝ)..x, 1 / (log t) := by
  admit

lemma inv_div_log_asy : ∃ c, ∀ᶠ (x : ℝ) in atTop,
    ∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2 ≤ c * (x / log x ^ 2) := by
  admit

lemma integral_log_inv_pialt (x : ℝ) (hx : 4 ≤ x) : ∫ (t : ℝ) in Set.Icc 2 x, 1 / log t =
    x / log x - 2 / log 2 + ∫ (t : ℝ) in Set.Icc 2 x, 1 / (log t) ^ 2 := by
  admit

lemma integral_div_log_asymptotic : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ᶠ (x : ℝ) in atTop, ∫ t in Set.Icc 2 x, 1 / (log t) = (1 + c x) * x / (log x) := by
  admit

/-- **pi-alt**

One has
  $$ \pi(x) = (1+o(1)) \frac{x}{\log x}$$
  as $x \to \infty$.

PROVIDED SOLUTION:
An integration by parts gives
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} - \frac{2}{\log 2} +
  \int_2^x \frac{dt}{\log^2 t}.$$
  We have the crude bounds
  $$ \int_2^{\sqrt{x}} \frac{dt}{\log^2 t} = O( \sqrt{x} )$$
  and
  $$ \int_{\sqrt{x}}^x \frac{dt}{\log^2 t} = O( \frac{x}{\log^2 x} )$$
  and combining all this we obtain
  $$ \int_2^x \frac{dt}{\log t} = \frac{x}{\log x} + O( \frac{x}{\log^2 x} )$$
  $$ = (1+o(1)) \frac{x}{\log x}$$
  and the claim then follows from Theorem \ref{pi_asymp}.
-/
theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  admit

theorem pi_alt' :
    (fun (x : ℝ) ↦ (primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x ↦ x / log x) := by
  admit

lemma pi_nth_prime (n : ℕ) :
    primeCounting (nth_prime n) = n + 1 := by
  admit

lemma tendsto_nth_prime_atTop : Tendsto nth_prime atTop atTop := by
  admit

lemma pi_nth_prime_asymp :
    (fun n ↦ (nth_prime n) / (log (nth_prime n))) ~[atTop] (fun (n : ℕ) ↦ (n : ℝ)) := by
  admit

lemma log_nth_prime_asymp : (fun n ↦ log (nth_prime n)) ~[atTop] (fun n ↦ log n) := by
  admit

lemma nth_prime_asymp : (fun n ↦ ((nth_prime n) : ℝ)) ~[atTop] (fun n ↦ n * log n) := by
  admit

/-- **pn-asymptotic**

One has
    $$ p_n = (1+o(1)) n \log n$$
  as $n \to \infty$.

PROVIDED SOLUTION:
Use Corollary \ref{pi_alt} to show that $n=\pi(p_n)\sim p_n/\log p_n$
    Taking logs gives $\log n \sim \log p_n - \log\log p_n \sim \log p_n$.
    Multiplying these gives $p_n\sim n\log n$ from which the result follows.
-/
theorem pn_asymptotic : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, n > 1 → Nat.nth Nat.Prime n = (1 + c n) * n * log n := by
  admit

/-- **pn-pn-plus-one**

We have $p_{n+1} - p_n = o(p_n)$
    as $n \to \infty$.

PROVIDED SOLUTION:
Easy consequence of preceding proposition.
-/
theorem pn_pn_plus_one : ∃ c : ℕ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ n : ℕ, Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n = (c n) * Nat.nth Nat.Prime n := by
  admit

lemma prime_in_gap' (a b : ℕ) (h : a.primeCounting < b.primeCounting)
    : ∃ (p : ℕ), p.Prime ∧ (a + 1) ≤ p ∧ p < (b + 1) := by
  admit

lemma prime_in_gap (a b : ℝ) (ha : 0 < a)
    (h : ⌊a⌋₊.primeCounting < ⌊b⌋₊.primeCounting)
    : ∃(p : ℕ), p.Prime ∧ a < p ∧ p ≤ b := by
  admit

lemma bound_f_second_term (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop, (1 + f x) < (1 + δ) := by
  admit

lemma bound_f_first_term {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ)
    (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x: ℝ in atTop, (1 + f ((1 + ε) * x)) > (1 - δ)  := by
  admit

lemma smaller_terms {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ)
    (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop, (1 - δ) * ((1 + ε) * x / (Real.log ((1 + ε) * x))) <
      (1 + f ((1 + ε) * x)) * ((1 + ε) * x / (Real.log ((1 + ε) * x))) := by
  admit

lemma second_smaller_terms (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop,
      (1 + δ) * (x / Real.log x) > (1 + f x) * (x / Real.log x) := by
  admit

lemma x_log_x_atTop : Filter.Tendsto (fun x => x / Real.log x) Filter.atTop Filter.atTop := by
  admit

lemma tendsto_by_squeeze (ε : ℝ) (hε : ε > 0) :
    Tendsto (fun (x : ℝ) => (Nat.primeCounting ⌊(1 + ε) * x⌋₊ : ℝ) -
      (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop atTop := by
  admit

/-- **prime-between**

For every $\eps>0$, there is a prime between $x$ and $(1+\eps)x$ for
  all sufficiently large $x$.

PROVIDED SOLUTION:
Use Corollary \ref{pi_alt} to show that $\pi((1+\eps)x) - \pi(x)$ goes to infinity
  as $x \to \infty$.
-/
theorem prime_between {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < (1 + ε) * x := by
  admit

/-- We have $|\sum_{n \leq x} \frac{\mu(n)}{n}| \leq 1$.

PROVIDED SOLUTION:
From M\"obius inversion $1_{n=1} = \sum_{d|n} \mu(d)$ and summing we have
    $$ 1 = \sum_{d \leq x} \mu(d) \lfloor \frac{x}{d} \rfloor$$
    for any $x \geq 1$. Since $\lfloor \frac{x}{d} \rfloor = \frac{x}{d} - \epsilon_d$ with
    $0 \leq \epsilon_d < 1$ and $\epsilon_x = 0$, we conclude that
    $$ 1 ≥ x \sum_{d \leq x} \frac{\mu(d)}{d} - (x - 1)$$
    and the claim follows.
-/
theorem sum_mobius_div_self_le (N : ℕ) : |∑ n ∈ range N, μ n / (n : ℚ)| ≤ 1 := by
  admit

lemma sum_mobius_mul_floor (x : ℝ) (hx : 1 ≤ x) :
  ∑ n ∈ Iic ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) * (⌊x/n⌋ : ℝ) = 1 := by
  admit

noncomputable def mu_log : ArithmeticFunction ℝ :=
    ⟨(fun n ↦ μ n * ArithmeticFunction.log n), (by admit)⟩

lemma mu_log_apply (n : ℕ) : mu_log n = μ n * ArithmeticFunction.log n := by
  admit

lemma mu_log_mul_zeta : mu_log * ArithmeticFunction.zeta = -Λ := by
  admit

lemma mu_log_eq_mu_mul_neg_lambda : mu_log = μ * -Λ := by
  admit

lemma ArithmeticFunction.neg_apply {R : Type*} [NegZeroClass R] {f : ArithmeticFunction R} {n : ℕ}
    : (-f) n = -f n := by
  admit

lemma sum_mu_Lambda (x : ℝ) : ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ) * log n = - ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * Psi (x/k) := by
  admit

lemma M_log_identity (x : ℝ) (hx : 1 ≤ x) : M x * log x = ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (log (x/k) - Psi (x/k)) := by
  admit

noncomputable def R (x : ℝ) : ℝ := Psi x - x

lemma R_isLittleO : R =o[atTop] id := by
  admit

lemma sum_mobius_div_isBigO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, (μ k : ℝ) * (x / k)) =O[atTop] id := by
  admit

lemma sum_log_div_isBigO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, log (x / k)) =O[atTop] id := by
  admit

lemma R_locally_bounded (K : ℝ) (hK : 0 ≤ K) : ∃ C, ∀ y ∈ Set.Icc 0 K, |R y| ≤ C := by
  admit

lemma sum_bounded_of_linear_bound {f : ℝ → ℝ} {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C) (h : ∀ y, 1 ≤ y → |f y| ≤ ε * y + C) (x : ℝ) (hx : 1 ≤ x) :
  ∑ k ∈ Icc 1 ⌊x⌋₊, |f (x / k)| ≤ ε * x * (log x + 1) + C * x := by
  admit

lemma sum_abs_R_isLittleO : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * log x) := by
  admit

lemma R_linear_bound (ε : ℝ) (hε : 0 < ε) : ∃ C, 0 ≤ C ∧ ∀ y, 1 ≤ y → |R y| ≤ ε * y + C := by
  admit

lemma sum_abs_R_isLittleO' : (fun x : ℝ => ∑ k ∈ Iic ⌊x⌋₊, |R (x / k)|) =o[atTop] (fun x => x * log x) := by
  admit

lemma M_isLittleO : M =o[atTop] id := by
  admit

lemma M_isLittleO' : M =o[atTop] id := by
  admit

/-- We have $\sum_{n \leq x} \mu(n) = o(x)$.

PROVIDED SOLUTION:
From the Dirichlet convolution identity
    $$ \mu(n) \log n = - \sum_{d|n} \mu(d) \Lambda(n/d)$$
  and summing we obtain
  $$ \sum_{n \leq x} \mu(n) \log n = - \sum_{d \leq x} \mu(d) \sum_{m \leq x/d} \Lambda(m).$$
  For any $\eps>0$, we have from the prime number theorem that
  $$ \sum_{m \leq x/d} \Lambda(m) = x/d + O(\eps x/d) + O_\eps(1)$$
  (divide into cases depending on whether $x/d$ is large or small compared to $\eps$).
  We conclude that
  $$ \sum_{n \leq x} \mu(n) \log n
    = - x \sum_{d \leq x} \frac{\mu(d)}{d} + O(\eps x \log x) + O_\eps(x).$$
  Applying (equation mun) we conclude that
  $$ \sum_{n \leq x} \mu(n) \log n = O(\eps x \log x) + O_\eps(x).$$
  and hence
  $$ \sum_{n \leq x} \mu(n) \log x
    = O(\eps x \log x) + O_\eps(x) + O( \sum_{n \leq x} (\log x - \log n) ).$$
  From Stirling's formula one has
  $$  \sum_{n \leq x} (\log x - \log n) = O(x)$$
  thus
  $$ \sum_{n \leq x} \mu(n) \log x = O(\eps x \log x) + O_\eps(x)$$
  and thus
  $$ \sum_{n \leq x} \mu(n) = O(\eps x) + O_\eps(\frac{x}{\log x}).$$
  Sending $\eps \to 0$ we obtain the claim.
-/
theorem mu_pnt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, μ n) =o[atTop] fun x ↦ x := by
  admit

lemma lambda_eq_sum_sq_dvd_mu (n : ℕ) (hn : n ≠ 0) :
    ((-1 : ℝ) ^ (Ω n)) = ∑ d ∈ (Icc 1 n).filter (fun d => d^2 ∣ n), (μ (n / d^2) : ℝ) := by
  admit

lemma sum_lambda_eq_sum_mu_div_sq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ((-1 : ℝ) ^ (Ω n)) =
    ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d^2), (μ k : ℝ) := by
  admit

lemma sum_mu_div_sq_isLittleO : (fun N : ℕ ↦ ∑ d ∈ Finset.Icc 1 (Nat.sqrt N), ∑ k ∈ Finset.Icc 1 (N / d^2), (μ k : ℝ)) =o[atTop] (fun N ↦ (N : ℝ)) := by
  admit

/-- We have $\sum_{n \leq x} \lambda(n) = o(x)$.

PROVIDED SOLUTION:
From the identity
    $$ \lambda(n) = \sum_{d^2|n} \mu(n/d^2)$$
  and summing, we have
  $$ \sum_{n \leq x} \lambda(n) = \sum_{d \leq \sqrt{x}} \sum_{n \leq x/d^2} \mu(n).$$
  For any $\eps>0$, we have from Proposition \ref{mu-pnt} that
  $$ \sum_{n \leq x/d^2} \mu(n) = O(\eps x/d^2) + O_\eps(1)$$
  and hence on summing in $d$
  $$ \sum_{n \leq x} \lambda(n) = O(\eps x) + O_\eps(x^{1/2}).$$
  Sending $\eps \to 0$ we obtain the claim.
-/
theorem lambda_pnt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (-1)^(Ω n)) =o[atTop] fun x ↦ x := by
  admit

lemma sum_mobius_floor (x : ℝ) (hx : 1 ≤ x) : ∑ n ∈ Icc 1 ⌊x⌋₊, (μ n : ℝ) * ⌊x / n⌋ = 1 := by
  admit

lemma sum_mobius_floor_tail_isLittleO (K : ℕ) (hK : 0 < K) :
    (fun x : ℝ => ∑ n ∈ Finset.Ioc ⌊x/K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)) =o[atTop] fun x => x := by
  admit

lemma sum_mobius_div_approx (x : ℝ) (K : ℕ) (hK : 0 < K) (hx : 1 ≤ x) :
  |x * (∑ n ∈ Icc 1 ⌊x/K⌋₊, (μ n : ℝ) / n) - 1| ≤ x/K + |∑ n ∈ Ioc ⌊x/K⌋₊ ⌊x⌋₊, (μ n : ℝ) * (⌊x / (n : ℝ)⌋ : ℝ)| := by
  admit

/-- We have $\sum_{n \leq x} \mu(n)/n = o(1)$.

PROVIDED SOLUTION:
As in the proof of Theorem \ref{mun}, we have
    $$ 1 = \sum_{d \leq x} \mu(d) \lfloor \frac{x}{d} \rfloor$$
    $$ = x \sum_{d \leq x} \frac{\mu(d)}{d} - \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \}$$
  so it will suffice to show that
  $$ \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \} = o(x).$$
  Let $N$  be a natural number.  It suffices to show that
  $$ \sum_{d \leq x} \mu(d) \{ \frac{x}{d} \} = O(x/N).$$
  if $x$ is large enough depending on $N$.
  We can split the left-hand side as the sum of
  $$ \sum_{d \leq x/N} \mu(d) \{ \frac{x}{d} \} $$
  and
  $$ \sum_{j=1}^{N-1} \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j).$$
  The first term is clearly $O(x/N)$.  For the second term, we can use Theorem \ref{mu-pnt}
  and summation by parts (using the fact that $x/d-j$ is monotone and bounded) to find that
  $$ \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j) = o(x)$$
  for any given $j$, so in particular
  $$ \sum_{x/(j+1) < d \leq x/j} \mu(d) (x/d - j) = O(x/N^2)$$
  for all $j=1,\dots,N-1$ if $x$ is large enough depending on $N$.
  Summing all the bounds, we obtain the claim.
-/
theorem mu_pnt_alt : (fun x : ℝ ↦ ∑ n ∈ range ⌊x⌋₊, (μ n : ℝ) / n) =o[atTop] fun _ ↦ (1 : ℝ) := by
  admit

/-!
# Consequences of the PNT in arithmetic progressions
-/
/-- **Prime number theorem in AP**

If $a\ (q)$ is a primitive residue class, then one has
  $$ \sum_{p \leq x: p = a\ (q)} \log p = \frac{x}{\phi(q)} + o(x).$$

PROVIDED SOLUTION:
This is a routine modification of the proof of Theorem \ref{chebyshev-asymptotic}.
-/
theorem chebyshev_asymptotic_pnt
    {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
    (fun x ↦ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0) ~[atTop]
      fun x ↦ x / q.totient := by
  admit

/-- **Dirichlet's theorem**

Any primitive residue class contains an infinite number of primes.

PROVIDED SOLUTION:
If this were not the case, then the sum $\sum_{p \leq x: p = a\ (q)} \log p$
  would be bounded in $x$, contradicting Theorem \ref{chebyshev-asymptotic-pnt}.
-/
theorem dirichlet_thm {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : Nat.Coprime a q) (ha' : a < q) :
    Infinite { p // p.Prime ∧ p % q = a } := by
  admit

/-!
# Consequences of the Chebotarev density theorem
-/

/-!
\begin{lemma}[Cyclotomic Chebotarev]  For any $a$ coprime to $m$,
$$ \sum_{N \mathfrak{p} \leq x; N \mathfrak{p} = a\ (m)} \log N \mathfrak{p}  =
\frac{1}{|G|} \sum_{N \mathfrak{p} \leq x} \log N \mathfrak{p}.$$
\end{lemma}
-/

/-!
\begin{proof}\uses{Dedekind-PNT, WeakPNT-AP} This should follow from Lemma \ref{Dedekind-PNT} by a Fourier expansion.
\end{proof}
-/
