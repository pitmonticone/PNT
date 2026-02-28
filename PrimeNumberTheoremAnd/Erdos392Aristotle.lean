import Mathlib
import PrimeNumberTheoremAnd.ConsequencesAristotle
import PrimeNumberTheoremAnd.LogTablesAristotle

namespace Erdos392

/-!
# Erdos problem 392

The proof here is adapted from https://www.erdosproblems.com/forum/thread/392\#post-2696 which
in turn is inspired by the arguments in https://arxiv.org/abs/2503.20170.
-/

open Finset Nat Real Multiset Asymptotics
/-- We work with (approximate) factorizations $a_1 \dots a_t$ of a factorial $n!$.
-/
structure Factorization (n : ℕ) where
  a : Multiset ℕ
  ha : ∀ m ∈ a, m ≤ n
  hpos : ∀ m ∈ a, 0 < m

def Factorization.sum {n : ℕ} (f : Factorization n) {R : Type*} [AddCommMonoid R]
    (F : ℕ → R) : R :=
  (f.a.map F).sum

def Factorization.prod {n : ℕ} (f : Factorization n) {R : Type*} [CommMonoid R]
    (F : ℕ → R) : R :=
  (f.a.map F).prod
/-- The waste of a factorizations $a_1 \dots a_t$ is defined as $\sum_i \log (n / a_i)$.
-/
noncomputable def Factorization.waste {n : ℕ} (f : Factorization n) : ℝ :=
  f.sum (fun m ↦ log (n / m : ℝ))
/-- The balance of a factorization $a_1 \dots a_t$ at a prime $p$ is defined as the number of
  times $p$ divides $a_1 \dots a_t$, minus the number of times $p$ divides $n!$.
-/
def Factorization.balance {n : ℕ} (f : Factorization n) (p : ℕ) : ℤ :=
  f.sum (fun m ↦ m.factorization p) - (n.factorial.factorization p:ℤ)
/-- The total imbalance of a factorization $a_1 \dots a_t$ is the sum of absolute values of
  the balances at each prime.
-/
def Factorization.total_imbalance {n : ℕ} (f : Factorization n) : ℕ :=
  ∑ p ∈ (n+1).primesBelow, (f.balance p).natAbs

/-- The factorization of a multiset product equals the sum of factorizations. -/
private lemma factorization_multiset_prod (s : Multiset ℕ) (h : (0 : ℕ) ∉ s) (p : ℕ) :
    s.prod.factorization p = (s.map (·.factorization p)).sum := by
  admit

/-- If a factorization has zero total imbalance, then it exactly factors $n!$.
-/
theorem Factorization.zero_total_imbalance {n : ℕ} (f : Factorization n)
    (hf : f.total_imbalance = 0) : f.prod id = n.factorial := by
  admit

/-- The waste of a factorization is equal to $t \log n - \log n!$, where $t$ is the
  number of elements.
-/
theorem Factorization.waste_eq {n : ℕ} (f : Factorization n) (hf : f.total_imbalance = 0) :
    f.a.card * (Real.log n) = Real.log n.factorial + f.waste := by
  admit

/-- The score of a factorization (relative to a cutoff parameter $L$) is equal to its waste,
  plus $\log p$ for every surplus prime $p$, $\log (n/p)$ for every deficit prime above $L$,
  $\log L$ for every deficit prime below $L$ and an additional $\log n$ if one is not in
  total balance.
-/
noncomputable def Factorization.score {n : ℕ} (f : Factorization n) (L : ℕ) : ℝ :=
  f.waste
  + (if f.total_imbalance > 0 then Real.log n else 0)
  + ∑ p ∈ (n+1).primesBelow,
    if f.balance p > 0 then (f.balance p) * (Real.log p)
    else if p ≤ L then (-f.balance p) * (Real.log L)
    else (-f.balance p) * (Real.log (n/p))
/-- If one is in total balance, then the score is equal to the waste.
-/
theorem Factorization.score_eq {n : ℕ} {f : Factorization n} (hf : f.total_imbalance = 0) (L : ℕ) :
    f.score L = f.waste := by
  admit

/-- Given a factorization `f`, an element `m` in it, and a new number `m' ≤ n`,
`replace` returns a new factorization with `m` replaced by `m'`. -/
def Factorization.replace {n : ℕ} (f : Factorization n) (m m' : ℕ)
    (_hm : m ∈ f.a) (hm' : m' ≤ n) (hm'_pos : 0 < m') : Factorization n where
  a := (f.a.erase m).cons m'
  ha x hx := by admit

  hpos x hx := by admit

/-- The sum of a function `F` over a factorization after replacing `m` with `m'`
equals the original sum minus `F m` plus `F m'`. -/
lemma Factorization.replace_sum {n : ℕ} (f : Factorization n) (m m' : ℕ)
    (hm : m ∈ f.a) (hm' : m' ≤ n) (hm'_pos : 0 < m') {R : Type*} [AddCommGroup R]
    (F : ℕ → R) :
    (f.replace m m' hm hm' hm'_pos).sum F = f.sum F - F m + F m' := by
  admit

/-- The balance of a prime `q` after replacing `m` with `m'` equals the original balance
minus the exponent of `q` in `m` plus the exponent of `q` in `m'`. -/
lemma Factorization.replace_balance {n : ℕ} (f : Factorization n) (m m' : ℕ)
    (hm : m ∈ f.a) (hm' : m' ≤ n) (hm'_pos : 0 < m') (q : ℕ) :
    (f.replace m m' hm hm' hm'_pos).balance q =
      f.balance q - m.factorization q + m'.factorization q := by
  admit

/-- If we replace `m` with `m/p` where `p` divides `m`, the balance of `p` decreases by 1,
and the balance of any other prime remains unchanged. -/
lemma Factorization.replace_div_balance {n : ℕ} (f : Factorization n) (m p : ℕ)
    (hm : m ∈ f.a) (h_fac_pos : 0 < m.factorization p) (hp : p.Prime) (q : ℕ) :
    let m' := m / p
    have hm' : m' ≤ n := (div_le_self m p).trans (f.ha m hm)
    have hm'_pos : 0 < m' := div_pos (le_of_dvd (f.hpos m hm)
      (hp.dvd_iff_one_le_factorization (f.hpos m hm).ne' |>.mpr h_fac_pos)) hp.pos
    (f.replace m m' hm hm' hm'_pos).balance q = if q = p then f.balance q - 1 else f.balance q := by
  admit

/-- Replacing `m` with `m/p` strictly decreases the total imbalance
when `p` has positive balance. -/
lemma Factorization.replace_div_total_imbalance {n : ℕ} (f : Factorization n) (m p : ℕ)
    (hm : m ∈ f.a) (h_fac_pos : 0 < m.factorization p) (hp : p.Prime)
    (hp_mem : p ∈ (n + 1).primesBelow) (h_bal_pos : f.balance p > 0) :
    let m' := m / p
    have hm' : m' ≤ n := (div_le_self m p).trans (f.ha m hm)
    have hm'_pos : 0 < m' := div_pos (le_of_dvd (f.hpos m hm)
      (hp.dvd_iff_one_le_factorization (f.hpos m hm).ne' |>.mpr h_fac_pos)) hp.pos
    (f.replace m m' hm hm' hm'_pos).total_imbalance < f.total_imbalance := by
  admit

/-- Replacing `m` with `m/p` decreases the score (or keeps it equal) if `p` has positive balance.
The waste increases by `log p`, but the sum term decreases by `log p`,
and the imbalance term is non-increasing. -/
lemma Factorization.replace_div_score_le {n : ℕ} (f : Factorization n) (m p : ℕ)
    (hm : m ∈ f.a) (h_fac_pos : 0 < m.factorization p) (hp : p.Prime)
    (hp_mem : p ∈ (n + 1).primesBelow) (_h_bal_pos : f.balance p > 0) (L : ℕ) :
    let m' := m / p
    have hm' : m' ≤ n := (div_le_self m p).trans (f.ha m hm)
    have hm'_pos : 0 < m' := div_pos (le_of_dvd (f.hpos m hm)
      (hp.dvd_iff_one_le_factorization (f.hpos m hm).ne' |>.mpr h_fac_pos)) hp.pos
    (f.replace m m' hm hm' hm'_pos).score L ≤ f.score L := by
  admit

/-- Extends a factorization by adding a new factor `m`. -/
def Factorization.addFactor {n : ℕ} (f : Factorization n) (m : ℕ) (hm : m ≤ n) (hm_pos : 0 < m) :
    Factorization n where
  a := cons m f.a
  ha x hx := by admit
  hpos x hx := by admit

/-- Adding a factor increases balance by the factor's factorization. -/
lemma Factorization.addFactor_balance {n : ℕ} (f : Factorization n) (m : ℕ) (hm : m ≤ n)
    (hm_pos : 0 < m) (p : ℕ) :
    (addFactor f m hm hm_pos).balance p = f.balance p + m.factorization p := by
  admit

/-- Adding a factor increases waste by `log (n / m)`. -/
lemma Factorization.addFactor_waste {n : ℕ} (f : Factorization n) (m : ℕ) (hm : m ≤ n)
    (hm_pos : 0 < m) : (addFactor f m hm hm_pos).waste = f.waste + Real.log (n / m) := by
  admit

/-- The multiset of deficit primes at most `L`, each repeated `|balance p|` times. -/
def Factorization.deficitMultiset {n : ℕ} (f : Factorization n) (L : ℕ) : Multiset ℕ :=
  ((n + 1).primesBelow.filter (fun p ↦ p ≤ L ∧ f.balance p < 0)).val.bind
    fun p ↦ replicate (f.balance p).natAbs p

/-- Elements of the deficit multiset are primes at most `L`. -/
lemma Factorization.mem_deficitMultiset {n : ℕ} (f : Factorization n) (L : ℕ) (q : ℕ) :
    q ∈ deficitMultiset f L → q.Prime ∧ q ≤ L := by
  admit

/-- Given a multiset of numbers `≤ L` with product `> n`, there exists a sub-multiset
whose product `m` satisfies `n / L < m ≤ n`. -/
lemma exists_submultiset_prod_between {n L : ℕ} (D : Multiset ℕ) (hL : 0 < L) (hn : 1 ≤ n)
    (hD_le : ∀ p ∈ D, p ≤ L) (hD_prod : D.prod > n) :
    ∃ M ≤ D, n < M.prod * L ∧ M.prod ≤ n := by
  admit

/-- A prime with negative balance is at most `n`. -/
lemma Factorization.deficit_implies_le_n {n : ℕ} (f : Factorization n) (p : ℕ)
    (hp : f.balance p < 0) : p ≤ n := by
  admit

/-- The factorization of a product of primes at `p` equals the count of `p` in the multiset. -/
lemma factorization_prod_eq_count {D : Multiset ℕ} (hD : ∀ p ∈ D, p.Prime) (p : ℕ) :
    D.prod.factorization p = D.count p := by
  admit

/-- The product of the deficit multiset is positive. -/
lemma Factorization.deficitMultiset_prod_pos {n : ℕ} (f : Factorization n) (L : ℕ) :
    0 < (deficitMultiset f L).prod := by
  admit

/-- The count of `p` in the deficit multiset equals `|balance p|` if `p` is a deficit prime
at most `L`, and `0` otherwise. -/
lemma Factorization.count_deficitMultiset {n : ℕ} (f : Factorization n) (L : ℕ) (p : ℕ) :
    (deficitMultiset f L).count p =
    if p ∈ (n + 1).primesBelow ∧ p ≤ L ∧ f.balance p < 0 then (f.balance p).natAbs else 0 := by
  admit

/-- Adding the full deficit multiset product to a factorization with no surplus primes and all
deficit primes at most `L` results in zero balance for all primes. -/
lemma Factorization.addFactor_deficit_balance_eq_zero {n : ℕ} (f : Factorization n) (L : ℕ)
    (h_surplus : ∀ p, f.balance p ≤ 0) (h_deficit_large : ∀ p, f.balance p < 0 → p ≤ L)
    (m : ℕ) (hm : m ≤ n) (hm_pos : 0 < m) (h_m_def : m = (deficitMultiset f L).prod) :
    ∀ p, (addFactor f m hm hm_pos).balance p = 0 := by
  admit

/-- Case 1 of `lower_score_3`: if the product of deficit primes is `≤ n`, adding the full
deficit multiset yields a factorization with zero imbalance and lower score. -/
lemma Factorization.lower_score_3_case1 {n : ℕ} (f : Factorization n) (L : ℕ)
    (h_surplus : ∀ p, f.balance p ≤ 0) (h_deficit_large : ∀ p, f.balance p < 0 → p ≤ L)
    (hf : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0)
    (h_prod : (deficitMultiset f L).prod ≤ n) :
    ∃ f' : Factorization n, f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  admit

/-- Adding a submultiset `M` of deficit primes to a factorization reduces the total imbalance
by `M.card`. -/
lemma Factorization.addFactor_submultiset_total_imbalance {n : ℕ} (f : Factorization n) (L : ℕ)
    (h_surplus : ∀ p, f.balance p ≤ 0) (M : Multiset ℕ) (hM : M ≤ deficitMultiset f L)
    (m : ℕ) (hm : m ≤ n) (hm_pos : 0 < m) (h_m_prod : m = M.prod) :
    (addFactor f m hm hm_pos).total_imbalance = f.total_imbalance - M.card := by
  admit

/-- The change in the score sum when one deficit prime `p` (with `p ≤ L`) has its balance
increased by 1 (still `≤ 0`). -/
lemma Factorization.score_sum_change {n : ℕ} (f f' : Factorization n) (L p : ℕ)
    (hp_mem : p ∈ (n + 1).primesBelow) (hp_le_L : p ≤ L) (h_bal_p : f.balance p < 0)
    (h_bal_p' : f'.balance p = f.balance p + 1)
    (h_bal_eq : ∀ q ∈ (n + 1).primesBelow, q ≠ p → f'.balance q = f.balance q) :
    (∑ q ∈ (n + 1).primesBelow,
      if f'.balance q > 0 then (f'.balance q) * Real.log q
      else if q ≤ L then (-f'.balance q) * Real.log L
      else (-f'.balance q) * Real.log (n / q)) -
    (∑ q ∈ (n + 1).primesBelow,
      if f.balance q > 0 then (f.balance q) * Real.log q
      else if q ≤ L then (-f.balance q) * Real.log L
      else (-f.balance q) * Real.log (n / q)) = -Real.log L := by
  admit

/-- The change in the score sum when a submultiset of deficit primes `M` is added. -/
lemma Factorization.score_sum_change_multiset {n : ℕ} (f f' : Factorization n) (L : ℕ)
    (M : Multiset ℕ) (hM_le : M ≤ deficitMultiset f L)
    (h_bal_eq : ∀ p ∈ (n + 1).primesBelow, f'.balance p = f.balance p + M.count p) :
    (∑ q ∈ (n + 1).primesBelow,
      if f'.balance q > 0 then (f'.balance q) * Real.log q
      else if q ≤ L then (-f'.balance q) * Real.log L
      else ↑(-f'.balance q) * Real.log (↑n / ↑q)) -
    (∑ q ∈ (n + 1).primesBelow,
      if f.balance q > 0 then ↑(f.balance q) * Real.log ↑q
      else if q ≤ L then (-f.balance q) * Real.log ↑L
      else ↑(-f.balance q) * Real.log (↑n / ↑q)) = -↑(M.card) * Real.log L := by
  admit

/-- Adding a submultiset `M` of deficit primes reduces the score if `n < M.prod * L`. -/
lemma Factorization.score_le_of_add_submultiset {n : ℕ} (f : Factorization n) (L : ℕ)
    (M : Multiset ℕ) (hM_le : M ≤ deficitMultiset f L)
    (m : ℕ) (hm : m ≤ n) (hm_pos : 0 < m) (h_m_prod : m = M.prod)
    (h_prod_gt : n < m * L) (hM_card_pos : 0 < M.card) (hL_ge_2 : 2 ≤ L) :
    (addFactor f m hm hm_pos).score L ≤ f.score L := by
  admit

/-- If there is a prime $p$ in surplus, one can remove it without increasing the
  score.

PROVIDED SOLUTION:
Locate a factor $a_i$ that contains the surplus prime $p$, then
  replace $a_i$ with $a_i/p$.
-/
theorem Factorization.lower_score_1 {n : ℕ} (f : Factorization n) (L : ℕ)
    (hf : ∃ p ∈ (n + 1).primesBelow, f.balance p > 0) :
    ∃ f' : Factorization n,
      f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  admit

/-- If there is a prime $p$ in deficit larger than $L$, one can remove it without
  increasing the score.

PROVIDED SOLUTION:
Add an additional factor of $p$ to the factorization.
-/
theorem Factorization.lower_score_2 {n : ℕ} (f : Factorization n) (L : ℕ)
    (hf : ∃ p ∈ (n + 1).primesBelow, p > L ∧ f.balance p < 0) :
    ∃ f' : Factorization n,
      f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  admit

/-- Case 2a of `lower_score_3`: If `L > n` and there is a deficit prime, we can add it to reduce
the score. -/
lemma Factorization.lower_score_3_case2a {n : ℕ} (f : Factorization n) (L : ℕ)
    (h_surplus : ∀ p, f.balance p ≤ 0)
    (hf : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0) (hL_gt_n : L > n) :
    ∃ f' : Factorization n,
      f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  admit

/-- Case 2b of `lower_score_3`: If `L ≤ n` and the product of deficit primes is `> n`,
we can find a submultiset to add that reduces the score. -/
lemma Factorization.lower_score_3_case2b {n : ℕ} (f : Factorization n) (L : ℕ)
    (h_surplus : ∀ p, f.balance p ≤ 0) (hf : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0)
    (h_prod : n < (deficitMultiset f L).prod) (hL_le_n : L ≤ n) :
    ∃ f' : Factorization n,
      f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  admit

/-- The clean case of `lower_score_3`, combining the three subcases. -/
lemma Factorization.lower_score_3_clean {n : ℕ} (f : Factorization n) (L : ℕ)
    (h_surplus : ∀ p, f.balance p ≤ 0) (h_deficit_large : ∀ p, f.balance p < 0 → p ≤ L)
    (hf : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0) :
    ∃ f' : Factorization n,
      f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  admit

/-- If there is a prime $p$ in deficit less than $L$, one can remove it without increasing the score.

PROVIDED SOLUTION:
Without loss of generality we may assume that one is not in the previous two
  situations, i.e., wlog there are no surplus primes and all primes in deficit are at most $L$.
  If all deficit primes multiply to $n$ or less, add that product to the factorization (this
  increases the waste by at most $\log n$, but we save a $\log n$ from now being in balance).
  Otherwise, greedily multiply all primes together while staying below $n$ until one cannot do so
  any further; add this product to the factorization, increasing the waste by at most $\log L$.
-/
theorem Factorization.lower_score_3 {n : ℕ} (f : Factorization n) (L : ℕ)
    (hf : ∃ p ∈ (n + 1).primesBelow, p ≤ L ∧ f.balance p < 0) :
    ∃ f' : Factorization n,
      f'.total_imbalance < f.total_imbalance ∧ f'.score L ≤ f.score L := by
  admit

/-- One can bring any factorization into balance without increasing the score.

PROVIDED SOLUTION:
Apply strong induction on the total imbalance of the factorization and use the
  previous three sublemmas.
-/
theorem Factorization.lowest_score {n : ℕ} (f : Factorization n) (L : ℕ) :
    ∃ f' : Factorization n, f'.total_imbalance = 0 ∧ f'.score L ≤ f.score L := by
  admit

/-- Starting from any factorization $f$, one can find a factorization $f'$ in balance whose
  cardinality is at most $\log n!$ plus the score of $f$, divided by $\log n$.

PROVIDED SOLUTION:
Combine Lemma \ref{score-lowest}, Lemma \ref{score-eq}, and
  Lemma \ref{waste-eq}.
-/
theorem Factorization.card_bound {n : ℕ} (f : Factorization n) (L : ℕ) : ∃ f' :
    Factorization n, f'.total_imbalance = 0 ∧ (f'.a.card : ℝ) * (Real.log n)
      ≤ Real.log n.factorial + (f.score L) := by
  admit

/-- Now let $M,L$ be additional parameters with $n > L^2$; we also need the minor
  variant $\lfloor n/L \rfloor > \sqrt{n}$.
-/
structure Params where
  n : ℕ
  M : ℕ
  L : ℕ
  hM : M > 1
  hL_pos : L > 0
  hL : n > L * L
  hL' : (n/L:ℕ) > Real.sqrt n  -- almost implied by hL, but not quite
  hL'' : 2 ≤ L
/-- We perform an initial factorization by taking the natural numbers between
  $n-n/M$ (inclusive) and $n$ (exclusive) repeated $M$ times, deleting those elements that are
  not $n/L$-smooth (i.e., have a prime factor greater than or equal to $n/L$).
-/
def Params.initial (P : Params) : Factorization P.n := {
  a := (replicate P.M (.Ico (P.n - P.n/P.M) P.n)).join.filter
    (fun m ↦ m ∈ (P.n/P.L).smoothNumbers)
  ha := fun m hm ↦ by
    simp only [Multiset.mem_filter, mem_join, mem_replicate] at hm
    obtain ⟨⟨_, ⟨_, rfl⟩, hs⟩, _⟩ := hm
    rw [Multiset.mem_Ico, tsub_le_iff_right] at hs
    grind
  hpos := fun m hm ↦ by
    simp only [Multiset.mem_filter, mem_join, mem_replicate] at hm
    obtain ⟨_, hsmooth⟩ := hm
    exact pos_of_ne_zero (mem_smoothNumbers.mp hsmooth).1
}
/-- The number of elements in this initial factorization is at most $n$.
-/
theorem Params.initial.card (P : Params) : P.initial.a.card ≤ P.n := by
  admit

/-- Elements of the initial factorization lie in the interval `[n - n/M, n)`. -/
lemma Params.initial.mem_range (P : Params) (m : ℕ) (hm : m ∈ P.initial.a) :
    P.n - P.n / P.M ≤ m ∧ m < P.n := by
  admit

/-- For elements `m` in the initial factorization, `n/m ≤ (1 - 1/M)⁻¹`. -/
lemma Params.initial.div_le (P : Params) (m : ℕ) (hm : m ∈ P.initial.a) :
    (P.n : ℝ) / m ≤ (1 - 1 / (P.M : ℝ))⁻¹ := by
  admit

/-- The total waste in this initial factorization is at most
  $n \log \frac{1}{1-1/M}$.
-/
theorem Params.initial.waste (P : Params) :
    P.initial.waste ≤ P.n * log (1 - 1/(P.M : ℝ))⁻¹ := by
  admit

/-- A large prime $p \geq n/L$ cannot be in surplus.

PROVIDED SOLUTION:
No such prime can be present in the factorization.
-/
theorem Params.initial.balance_large_prime_le (P : Params) {p : ℕ} (hp : p ≥ P.n / P.L) :
    P.initial.balance p ≤ 0 := by
  admit

/-- For primes `p > √n`, the `p`-adic valuation of `n!` equals `⌊n/p⌋`. This follows from
Legendre's formula since `p² > n` implies all higher power terms vanish. -/
lemma Params.initial.factorial_factorization_eq_div {n p : ℕ} (hp : p.Prime)
    (h_sqrt : p > Real.sqrt n) :
    (n.factorial).factorization p = n / p := by
  admit

/-- A large prime $p \geq n/L$ can be in deficit by at most $n/p$.

PROVIDED SOLUTION:
This is the number of times $p$ can divide $n!$.
-/
theorem Params.initial.balance_large_prime_ge (P : Params) {p : ℕ}
    (hp : p ≥ P.n / P.L) : P.initial.balance p ≥ -(P.n / p) := by
  admit

/-- The number of multiples of `p` in `[A, B)` is at most `⌈(B - A)/p⌉`, computed as
`(B - A + p - 1) / p`. -/
lemma Params.initial.count_multiples_le (A B p : ℕ) (hp : p > 0) :
    (Finset.filter (p ∣ ·) (Finset.Ico A B)).card ≤ (B - A + p - 1) / p := by
  admit

/-- An auxiliary bound `M · ⌈(n/M)/p⌉ ≤ ⌊n/p⌋ + M`, where the ceiling is computed as
`(n/M + p - 1) / p`. -/
lemma Params.initial.count_bound_aux (n M p : ℕ) (hp : p > 0) :
    M * ((n / M + p - 1) / p) ≤ n / p + M := by
  admit

/-- For primes `p > √n`, the sum of `p`-adic valuations in the initial factorization is bounded by
`M` times the count of multiples of `p` in `[n - n/M, n)`. -/
lemma Params.initial.sum_valuation_le_M_mul_interval_count (P : Params) {p : ℕ}
    (hp' : (p : ℝ) > Real.sqrt P.n) : (P.initial.a.map (·.factorization p)).sum ≤
      P.M * (Finset.filter (p ∣ ·) (Finset.Ico (P.n - P.n / P.M) P.n)).card := by
  admit

/-- A medium prime $\sqrt{n} < p ≤ n/L$ can be in surplus by at most $M$.

PROVIDED SOLUTION:
Routine computation using Legendre's formula.
-/
theorem Params.initial.balance_medium_prime_le (P : Params) {p : ℕ} (hp : p > Real.sqrt P.n) :
    P.initial.balance p ≤ P.M := by
  admit

/-- If `√n < p < n/L` and `p ∣ m` with `0 < m < n`, then `m` is `(n/L)`-smooth. -/
lemma Params.initial.smooth_of_multiple (P : Params) {p m : ℕ} (hp : p > Real.sqrt P.n)
    (hps : p < P.n / P.L) (hm : m < P.n) (hm0 : m ≠ 0) (hpm : p ∣ m) :
    m ∈ smoothNumbers (P.n / P.L) := by
  admit

/-- For `√n < p` prime and `p ∣ m` with `0 < m < n`, we have `ν_p(m) = 1` since `p² > n ≥ m`. -/
lemma Params.initial.valuation_eq_one (P : Params) {p m : ℕ} (hp : p.Prime)
    (hp' : p > Real.sqrt P.n) (hm : m < P.n) (hm0 : m ≠ 0) (hpm : p ∣ m) :
    m.factorization p = 1 := by
  admit

/-- The interval `[n - n/M, n)` contains at least `⌊n/M⌋/p` multiples of `p`. -/
lemma Params.initial.count_multiples_lower_bound (n M p : ℕ) (hM : M > 0) (hp : p > 0) :
    M * (Finset.filter (p ∣ ·) (Finset.Ico (n - n / M) n)).card + M ≥ n / p := by
  admit

/-- For `√n < p < n/L` and `0 < m < n`: smooth `m` has `ν_p(m) = 1` iff `p ∣ m`. -/
lemma Params.initial.valuation_eq_indicator (P : Params) {p m : ℕ} (hp : p.Prime)
    (hp' : p > Real.sqrt P.n) (hps : p < P.n / P.L) (hm : m < P.n) (hm0 : m ≠ 0) :
    (if m ∈ smoothNumbers (P.n / P.L) then m.factorization p else 0) =
      if p ∣ m then 1 else 0 := by
  admit

/-- For `√n < p < n/L`, `∑_{a ∈ initial.a} ν_p(a) = M · #{m ∈ [n-n/M, n) : p ∣ m}`. -/
lemma Params.initial.sum_valuation_eq (P : Params) {p : ℕ} (hp : p.Prime)
    (hp' : p > Real.sqrt P.n) (hps : p < P.n / P.L) : (P.initial.a.map (·.factorization p)).sum =
    P.M * (Finset.filter (p ∣ ·) (Finset.Ico (P.n - P.n / P.M) P.n)).card := by
  admit

/-- A medium prime $\sqrt{n} < p ≤ n/L$ can be in deficit by at most $M$.

PROVIDED SOLUTION:
The number of times $p$ divides $a_1 \dots a_t$ is at least $M \lfloor n/Mp
  \rfloor ≥ n/p - M$ (note that the removal of the non-smooth numbers does not remove any multiples
  of $p$).  Meanwhile, the number of times $p$ divides $n!$ is at most $n/p$.
-/
theorem Params.initial.balance_medium_prime_ge (P : Params) {p : ℕ} (hp : p < P.n / P.L)
    (hp' : p > Real.sqrt P.n) : P.initial.balance p ≥ -P.M := by
  admit

/-- The sum of `p`-adic valuations of numbers in an interval equals the sum over `k` of the count of
multiples of `p^k` in that interval. -/
lemma sum_factorization_eq_sum_multiples {A B p : ℕ} (hp : p.Prime) (hA : 0 < A) :
    ∑ m ∈ .Ico A B, m.factorization p =
      ∑ k ∈ .Ico 1 B, ((Finset.Ico A B).filter (p ^ k ∣ ·)).card := by
  admit

/-- The contribution of the `k`-th power of `p` to the balance is bounded by `M`.
Specifically, `M * count(p^k) ≤ floor(n/p^k) + M`. -/
lemma Params.initial.term_bound (P : Params) {p k : ℕ} (hp : p.Prime) :
    P.M * ((Finset.Ico (P.n - P.n / P.M) P.n).filter (p ^ k ∣ ·)).card ≤
      P.n / p ^ k + P.M := by
  admit

/-- The sum of valuations in the initial factorization is bounded by `M` times the sum of
valuations in the interval. This is because the initial factorization is a subset of `M` copies
of the interval. -/
lemma Params.initial.sum_valuation_le (P : Params) (p : ℕ) :
    (initial P).sum (fun m ↦ m.factorization p) ≤
      P.M * ∑ m ∈ .Ico (P.n - P.n / P.M) P.n, m.factorization p := by
  admit

/-- A small prime $p \leq \sqrt{n}$ can be in surplus by at most $M\log n$.

PROVIDED SOLUTION:
Routine computation using Legendre's formula, noting that at most
  $\log n / \log 2$ powers of $p$ divide any given number up to $n$.
-/
theorem Params.initial.balance_small_prime_le (P : Params) {p : ℕ} :
    P.initial.balance p ≤ P.M * (Real.log P.n) / (Real.log 2):= by
  admit

/-- If `p` is a small prime (`L < p ≤ √n`) and `m` is in the initial interval and divisible by `p`,
then `m` is `(n/L)`-smooth. -/
lemma Params.initial.smooth_of_dvd_small_prime (P : Params) {p m : ℕ} (hp : p ≤ Real.sqrt P.n)
    (hpL : p > P.L) (hm : m ∈ Finset.Ico (P.n - P.n / P.M) P.n) (hpm : p ∣ m) :
    m ∈ (P.n / P.L).smoothNumbers := by
  admit

/-- For a small prime `p`, the sum of `p`-adic valuations in the initial factorization equals `M`
times the sum over `k` of the count of multiples of `p^k` in the interval. -/
lemma Params.initial.sum_valuation_eq_small (P : Params) {p : ℕ} (hp : p.Prime)
    (hp_le : p ≤ Real.sqrt P.n) (hp_gt : p > P.L) :
    (P.initial.a.map (·.factorization p)).sum =
    P.M * ∑ k ∈ Finset.Ico 1 (Nat.log p P.n + 1),
      (Finset.filter (p^k ∣ ·) (Finset.Ico (P.n - P.n / P.M) P.n)).card := by
  admit

/-- The balance of a small prime `p` is at least `-M * floor(log_p n)`. -/
lemma Params.initial.balance_ge_neg_M_mul_log (P : Params) {p : ℕ} (hp : p.Prime)
    (hp_le : p ≤ Real.sqrt P.n) (hp_gt : p > P.L) :
    P.initial.balance p ≥ - (P.M * (Nat.log p P.n) : ℤ) := by
  admit

/-- A small prime $L < p \leq \sqrt{n}$ can be in deficit by at most
  $M\log n$.

PROVIDED SOLUTION:
Routine computation using Legendre's formula, noting that at most
  $\log n / \log 2$ powers of $p$ divide any given number up to $n$.
-/
theorem Params.initial.balance_small_prime_ge (P : Params) {p : ℕ} (hp : p ≤ Real.sqrt P.n)
    (hp' : p > P.L) : P.initial.balance p ≥ - P.M * (Real.log P.n) / (Real.log 2) := by
  admit

/-- The factorization consisting of `M` copies of `[n - n/M, n)`, without filtering for smooth
numbers. -/
def Params.initial_full (P : Params) : Factorization P.n where
  a := (replicate P.M (Finset.Ico (P.n - P.n / P.M) P.n).val).join
  ha m hm := by admit

  hpos m hm := by admit

/-- The set of numbers in `[n - n/M, n)` that are not `(n/L)`-smooth. -/
def Params.rough_set (P : Params) : Finset ℕ :=
  (Finset.Ico (P.n - P.n / P.M) P.n).filter (· ∉ (P.n / P.L).smoothNumbers)

/-- The balance of `initial_full` at prime `p` is `M` times the sum of valuations in the interval,
minus the valuation of `n!`. -/
lemma Params.initial_full_balance_eq (P : Params) (p : ℕ) :
    (initial_full P).balance p =
      (P.M : ℤ) * (∑ m ∈ Finset.Ico (P.n - P.n / P.M) P.n, (m.factorization p : ℤ)) -
        (P.n.factorial.factorization p : ℤ) := by
  admit

/-- The number of multiples of `p^k` in `[n - n/M, n)` times `M` is at least `n / p^k - M`. -/
lemma Params.initial.count_multiples_lower_bound_pow (n M p k : ℕ) (hM : M > 0) (hp : p > 0) :
    M * (filter (p ^ k ∣ ·) (Finset.Ico (n - n / M) n)).card + M ≥ n / p ^ k := by
  admit

/-- The term-wise bound `M · Cₖ - ⌊n/p^k⌋ ≥ -M`. -/
lemma Params.initial_full_term_bound (P : Params) (p k : ℕ) (hp : p > 0) :
    (P.M : ℤ) * (filter (p ^ k ∣ ·) (Finset.Ico (P.n - P.n / P.M) P.n)).card - (P.n / p ^ k : ℤ) ≥ -P.M := by
  admit

/-- The sum of valuations in `[n - n/M, n)` equals `∑ k ∈ [1, log_p n], #{m ∈ I | p^k ∣ m}`. -/
lemma Params.initial_full_sum_valuation_eq (P : Params) (p : ℕ) (hp : p.Prime) :
    ∑ m ∈ Finset.Ico (P.n - P.n / P.M) P.n, (m.factorization p : ℤ) =
    ∑ k ∈ Finset.Ico 1 (Nat.log p P.n + 1), ((filter (p ^ k ∣ ·) (Finset.Ico (P.n - P.n / P.M) P.n)).card : ℤ) := by
  admit

/-- The balance of `initial_full` is at least `-M · log n / log 2`. -/
lemma Params.initial_full_balance_ge (P : Params) (p : ℕ) (hp : p.Prime) :
    (initial_full P).balance p ≥ -P.M * Real.log P.n / Real.log 2 := by
  admit

/-- The balance of `initial` equals that of `initial_full` minus `M` times the sum of valuations
in `rough_set`. -/
lemma Params.initial_balance_eq (P : Params) (p : ℕ) :
    P.initial.balance p = (initial_full P).balance p -
      (P.M : ℤ) * ∑ m ∈ rough_set P, (m.factorization p : ℤ) := by
  admit

/-- If `m` is in the rough set, it has a prime factor `q ≥ n / L`. -/
lemma Params.exists_large_prime_of_rough (P : Params) (m : ℕ) (hm : m ∈ rough_set P) :
    ∃ q, q.Prime ∧ q ≥ P.n / P.L ∧ q ∣ m := by
  admit

/-- If a prime `q ≥ n / L` divides `m < n`, then its valuation in `m` is `1`. -/
lemma Params.valuation_eq_one_of_large_prime (P : Params) (m q : ℕ) (hm : m < P.n)
    (hm_pos : m ≠ 0) (hq : q.Prime) (hq_ge : q ≥ P.n / P.L) (hdiv : q ∣ m) :
    m.factorization q = 1 := by
  admit

/-- Any `m` in the rough set can be written as `q * k` where `q` is a prime `≥ n / L` and
`k ≤ L`, with `m.factorization q = 1`. -/
lemma Params.rough_set_structure (P : Params) (m : ℕ) (hm : m ∈ rough_set P) :
    ∃ q k, q.Prime ∧ q ≥ P.n / P.L ∧ k ≤ P.L ∧ m = q * k ∧ m.factorization q = 1 := by
  admit

/-- The prime factor `q ≥ n / L` of an element of `rough_set`, chosen via `rough_set_structure`. -/
noncomputable def Params.rough_q (P : Params) (m : ℕ) : ℕ :=
  if h : m ∈ rough_set P then (rough_set_structure P m h).choose else 0

/-- The cofactor `k ≤ L` of an element of `rough_set`, chosen via `rough_set_structure`. -/
noncomputable def Params.rough_k (P : Params) (m : ℕ) : ℕ :=
  if h : m ∈ rough_set P then (rough_set_structure P m h).choose_spec.choose else 0

/-- Properties of `rough_q` and `rough_k`: the prime `q` satisfies `q ≥ n / L`, the cofactor `k`
satisfies `k ≤ L`, we have `m = q * k`, and `m.factorization q = 1`. -/
lemma Params.rough_qk_prop (P : Params) (m : ℕ) (h : m ∈ rough_set P) :
    let q := rough_q P m
    let k := rough_k P m
    q.Prime ∧ q ≥ P.n / P.L ∧ k ≤ P.L ∧ m = q * k ∧ m.factorization q = 1 := by
  admit

/-- The cardinality of `rough_set` is at most `π(n) * L`. -/
lemma Params.rough_set_card_le (P : Params) :
    (rough_set P).card ≤ (Nat.primeCounting P.n) * P.L := by
  admit

/-- For `m ∈ rough_set` and `p ≤ L`, `vₚ(m) = vₚ(k)`. -/
lemma Params.rough_valuation_eq_k_valuation (P : Params) (m : ℕ) (hm : m ∈ rough_set P)
    (p : ℕ) (hp : p ≤ P.L) : m.factorization p = (rough_k P m).factorization p := by
  admit

/-- For `m ∈ rough_set` and `p ≤ L`, `vₚ(m) ≤ logₚ L`. -/
lemma Params.rough_valuation_le_log (P : Params) (m : ℕ) (hm : m ∈ rough_set P) (p : ℕ)
    (hp : p ≤ P.L) (hp_prime : p.Prime) : m.factorization p ≤ Nat.log p P.L := by
  admit

/-- The sum of valuations of `p` in `rough_set` is at most `π(n) * L * logₚ L`. -/
lemma Params.rough_valuation_sum_le (P : Params) (p : ℕ) (hp : p ≤ P.L) (hp_prime : p.Prime) :
    ∑ m ∈ rough_set P, m.factorization p ≤ primeCounting P.n * P.L * log p P.L := by
  admit

/-- Since `p ≥ 2` and `L ≥ 1`, `logₚ L < L`, so `L - logₚ L ≥ 1`. -/
lemma Params.L_sub_log_ge_one (P : Params) (p : ℕ) (hp : p.Prime) : (P.L : ℝ) - log p P.L ≥ 1 := by
  admit

/-- `π(n) ≥ log n` for `n ≥ 2`. -/
lemma Params.primeCounting_ge_log (n : ℕ) (hn : n ≥ 2) : (n.primeCounting : ℝ) ≥ Real.log n := by
  admit

/-- `π(n) * L * (L - logₚ L) ≥ log n * (1 / log 2 - 1)`. -/
lemma Params.balance_inequality_aux (P : Params) (p : ℕ) (hp_prime : p.Prime) :
    (P.n.primeCounting : ℝ) * P.L * (P.L - Nat.log p P.L) ≥
      Real.log P.n * (1 / Real.log 2 - 1) := by
  admit

/-- A tiny prime $p \leq L$ can be in deficit by at most $M\log n + ML\pi(n)$.

PROVIDED SOLUTION:
In addition to the Legendre calculations, one potentially removes factors of the
  form $plq$ with $l \leq L$ and $q \leq n$ a prime up to $M$ times each, with at most $L$ copies
  of $p$ removed at each factor.
-/
theorem Params.initial.balance_tiny_prime_ge (P : Params) {p : ℕ} (hp : p ≤ P.L) :
    P.initial.balance p ≥ -P.M * Real.log P.n - P.M * P.L ^ 2 * primeCounting P.n := by
  admit

private lemma Params.initial.score_bound_aux_balanced (P : Params)
    (hImb : P.initial.total_imbalance = 0) :
    (if P.initial.total_imbalance > 0 then Real.log P.n else 0) +
    ∑ p ∈ (P.n + 1).primesBelow,
      (if P.initial.balance p > 0 then (P.initial.balance p : ℝ) * Real.log p
       else if p ≤ P.L then -(P.initial.balance p : ℝ) * Real.log P.L
       else -(P.initial.balance p : ℝ) * Real.log (P.n / p)) ≤
    ∑ _ ∈ Finset.filter (·.Prime) (Finset.Iic (P.n / P.L)), P.M * Real.log P.n +
    (∑ _ ∈ Finset.filter (·.Prime) (Finset.Iic ⌊(Real.sqrt P.n)⌋₊),
        P.M * Real.log P.n * Real.log P.n / Real.log 2 +
    (∑ p ∈ Finset.filter (·.Prime) (Finset.Icc (P.n / P.L) P.n),
        (P.n / p) * Real.log (P.n / p) +
    ∑ _ ∈ Finset.filter (·.Prime) (Finset.Iic P.L),
        (P.M * Real.log P.n + P.M * P.L^2 * primeCounting P.n) * Real.log P.L)) := by
  admit

private lemma Params.initial.score_bound_aux_imbalanced (P : Params)
    (hImb : P.initial.total_imbalance > 0) :
    (if P.initial.total_imbalance > 0 then Real.log P.n else 0) +
    ∑ p ∈ (P.n + 1).primesBelow,
      (if P.initial.balance p > 0 then (P.initial.balance p : ℝ) * Real.log p
       else if p ≤ P.L then -(P.initial.balance p : ℝ) * Real.log P.L
       else -(P.initial.balance p : ℝ) * Real.log (P.n / p)) ≤
    ∑ _ ∈ Finset.filter (·.Prime) (Finset.Iic (P.n / P.L)), P.M * Real.log P.n +
    (∑ _ ∈ Finset.filter (·.Prime) (Finset.Iic ⌊(Real.sqrt P.n)⌋₊),
        P.M * Real.log P.n * Real.log P.n / Real.log 2 +
    (∑ p ∈ Finset.filter (·.Prime) (Finset.Icc (P.n / P.L) P.n),
        (P.n / p) * Real.log (P.n / p) +
    ∑ _ ∈ Finset.filter (·.Prime) (Finset.Iic P.L),
        (P.M * Real.log P.n + P.M * P.L^2 * primeCounting P.n) * Real.log P.L)) := by
  admit

/-- The initial score is bounded by
  $$ n \log(1-1/M)^{-1} + \sum_{p \leq n/L} M \log n + \sum_{p \leq \sqrt{n}} M \log^2 n / \log 2
  + \sum_{n/L < p \leq n} \frac{n}{p} \log \frac{n}{p}
  + \sum_{p \leq L} (M \log n + M L \pi(n)) \log L.$$

PROVIDED SOLUTION:
Combine Lemma \ref{initial-factorization-waste},
  Sublemma \ref{initial-factorization-large-prime-le},
  Sublemma \ref{initial-factorization-large-prime-ge},
  Sublemma \ref{initial-factorization-medium-prime-le},
  Sublemma \ref{initial-factorization-medium-prime-ge},
  Sublemma \ref{initial-factorization-small-prime-le},
  Sublemma \ref{initial-factorization-small-prime-ge}, and
  Sublemma \ref{initial-factorization-tiny-prime-ge}, and combine $\log p$ and $\log (n/p)$ to $\log n$.
-/
theorem Params.initial.score_bound (P : Params) :
    P.initial.score P.L ≤ P.n * log (1 - 1 / (P.M : ℝ))⁻¹ +
      ∑ _ ∈ Finset.filter (·.Prime) (Finset.Iic (P.n / P.L)), P.M * Real.log P.n +
      ∑ _ ∈ Finset.filter (·.Prime) (Finset.Iic ⌊(Real.sqrt P.n)⌋₊),
        P.M * Real.log P.n * Real.log P.n / Real.log 2 +
      ∑ p ∈ Finset.filter (·.Prime) (Finset.Icc (P.n / P.L) P.n),
        (P.n / p) * Real.log (P.n / p) +
      ∑ _ ∈ Finset.filter (·.Prime) (Finset.Iic P.L),
        (P.M * Real.log P.n + P.M * P.L^2 * primeCounting P.n) * Real.log P.L := by
  admit

/-- If $M$ is sufficiently large depending on $\varepsilon$, then
$n \log(1-1/M)^{-1} \leq \varepsilon n$.

PROVIDED SOLUTION:
Use the fact that $\log(1-1/M)^{-1}$ goes to zero as $M \to \infty$.
-/
theorem Params.initial.bound_score_1 (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ M in .atTop, ∀ P : Params,
      P.M = M → P.n * log (1 - 1 / (P.M : ℝ))⁻¹ ≤ ε * P.n := by
  admit

/-- If $L$ is sufficiently large depending on $M, \varepsilon$, and $n$
  sufficiently large depending on $L$, then $\sum_{p \leq n/L} M \log n  \leq \varepsilon n$.

PROVIDED SOLUTION:
Use the prime number theorem (or the Chebyshev bound).
-/
theorem Params.initial.bound_score_2 (ε : ℝ) (hε : ε > 0) (M : ℕ) :
    ∀ᶠ L in .atTop, ∀ᶠ n in .atTop, ∀ P : Params,
      P.L = L → P.n = n → P.M = M → ∑ _p ∈ Finset.filter (·.Prime) (Finset.Iic (P.n / P.L)),
        P.M * Real.log P.n ≤ ε * P.n := by
  admit

/-- If $n$ sufficiently large depending on $M, \varepsilon$, then
  $\sum_{p \leq \sqrt{n}} M \log^2 n / \log 2 \leq \varepsilon n$.

PROVIDED SOLUTION:
Crude estimation.
-/
theorem Params.initial.bound_score_3 (ε : ℝ) (hε : ε > 0) (M : ℕ) :
    ∀ᶠ n in .atTop, ∀ P : Params,
      P.M = M → P.n = n → ∑ _p ∈ filter (·.Prime) (Finset.Iic ⌊(Real.sqrt P.n)⌋₊),
          P.M * Real.log P.n * Real.log P.n / Real.log 2 ≤ ε * P.n := by
  admit

/-- The product `∏ p ≤ n, (1 - 1/p)` over primes tends to zero as `n → ∞`. -/
lemma prod_one_sub_one_div_prime_tendsto_zero :
    Filter.Tendsto (fun n ↦ ∏ p ∈ filter Prime (range n), (1 - 1 / (p : ℝ))) .atTop (nhds 0) := by
  admit

/-- For any `ε > 0`, there exists `a ≠ 0` with `φ(a)/a < ε`. -/
lemma exists_phi_div_self_lt {ε : ℝ} (hε : 0 < ε) : ∃ a : ℕ, a ≠ 0 ∧ (a.totient : ℝ) / a < ε := by
  admit

/-- $$\pi(n) = o(n) \quad \text{as } n \to \infty.$$

PROVIDED SOLUTION:
Given $\varepsilon > 0$, choose $a \neq 0$ with $\varphi(a)/a < \varepsilon/2$
(using $\prod_{p \leq n}(1 - 1/p) \to 0$). For $n \geq a + 2$,
$$\pi(n) \leq \frac{\varphi(a)}{a} \cdot n + \varphi(a) + \pi(a+1) + 1.$$
Since $\varphi(a)/a < \varepsilon/2$, for $n$ large enough the constant terms are absorbed,
giving $\pi(n) < \varepsilon n$.
-/
lemma primeCounting_is_o_id :
    IsLittleO .atTop (fun n ↦ (primeCounting n : ℝ)) (fun n ↦ (n : ℝ)) := by
  admit

lemma large_range_split (n L : ℕ) :
    Finset.Icc (n / L) n = insert (n / L) (Finset.Icc (n / L + 1) n) := by
  admit

lemma large_prime_sum_split (n L : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (n / L) n), f p =
      (if (n / L).Prime then f (n / L) else 0) +
      ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (n / L + 1) n), f p := by
  admit

lemma boundary_term_le (P : Params) :
    (if (P.n / P.L).Prime then
      ((P.n : ℝ) / (P.n / P.L : ℕ)) * Real.log ((P.n : ℝ) / (P.n / P.L : ℕ))
    else 0) ≤ (P.L + 1) * Real.log (P.L + 1) := by
  admit

/-- If $n$ sufficiently large depending on $L, \varepsilon$, then
$\sum_{n/L < p \leq n} \frac{n}{p} \log \frac{n}{p} \leq \varepsilon n$.

PROVIDED SOLUTION:
Bound $\frac{n}{p}$ by $L$ and use the prime number theorem (or the Chebyshev bound).
-/
theorem Params.initial.bound_score_4 (ε : ℝ) (hε : ε > 0) (L : ℕ) :
    ∀ᶠ n in .atTop, ∀ P : Params, P.L = L → P.n = n → ∑ p ∈ filter (·.Prime) (Icc (P.n / P.L + 1) P.n),
      (P.n / p) * Real.log (P.n / p) ≤ ε * P.n := by
  admit

/-- For all $n \geq 2$, one has $$\pi(n) \leq \sqrt{n} + \frac{2n \log 4}{\log n}.$$

PROVIDED SOLUTION:
By Chebyshev's bound, $\prod_{p \leq n} p \leq 4^n$, so
$\sum_{p \leq n} \log p \leq n \log 4$. The number of primes $p \leq \sqrt{n}$ is trivially
at most $\sqrt{n}$. For primes $p > \sqrt{n}$, we have $\log p > \frac{1}{2} \log n$, hence
$$\bigl(\pi(n) - \pi(\sqrt{n})\bigr) \cdot \tfrac{1}{2} \log n
  < \sum_{\sqrt{n} < p \leq n} \log p \leq n \log 4,$$
giving $\pi(n) - \pi(\sqrt{n}) < \frac{2n \log 4}{\log n}$. Adding $\pi(\sqrt{n}) \leq \sqrt{n}$
yields the result.
-/
lemma primeCounting_le_bound (n : ℕ) (hn : 2 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ Real.sqrt n + (2 * n * Real.log 4) / Real.log n := by
  admit

/-- The ratio `π(n) / n → 0` as `n → ∞`. -/
lemma tendsto_primeCounting_div_id_zero :
    Filter.Tendsto (fun n ↦ (Nat.primeCounting n : ℝ) / n) .atTop (nhds 0) := by
  admit

/-- If $n$ sufficiently large depending on $M, L, \varepsilon$, then
$\sum_{p \leq L} (M \log n + M L \pi(n)) \log L \leq \varepsilon n$.

PROVIDED SOLUTION:
Use the prime number theorem (or the Chebyshev bound).
-/
theorem Params.initial.bound_score_5 (ε : ℝ) (hε : ε > 0) (M L : ℕ) :
    ∀ᶠ n in Filter.atTop, ∀ P : Params,
      P.M = M → P.L = L → P.n = n → ∑ _p ∈ Finset.filter (·.Prime) (Finset.Iic P.L),
          (P.M * Real.log P.n + P.M * P.L^2 * primeCounting P.n) * Real.log P.L ≤ ε * P.n := by
  admit

/-- The score of the initial factorization can be taken to be $o(n)$.

PROVIDED SOLUTION:
Pick $M$ large depending on $\varepsilon$, then $L$ sufficiently large depending
  on $M, \varepsilon$, then $n$ sufficiently large depending on $M,L,\varepsilon$, so that the
  bounds in Sublemma \ref{bound-score-1}, Sublemma \ref{bound-score-2},
  Sublemma \ref{bound-score-3}, Sublemma \ref{bound-score-4}, and Sublemma \ref{bound-score-5}
  each contribute at most $(\varepsilon/5) n$.  Then use Proposition \ref{initial-score-bound}.
-/
theorem Params.initial.score (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ n in .atTop, ∃ P : Params, P.n = n ∧ P.initial.score P.L ≤ ε * n := by
  admit

/-- One can find a balanced factorization of $n!$ with cardinality at most
  $n - n / \log n + o(n / \log n)$.-

PROVIDED SOLUTION:
Combine Proposition \ref{initial-score} with Proposition \ref{card-bound} and
  the Stirling approximation.
-/
theorem Solution_1 (ε : ℝ) (hε : ε > 0) : ∀ᶠ n in .atTop, ∃ f : Factorization n,
    f.total_imbalance = 0 ∧ f.a.card ≤ n - n / Real.log n + ε * n / Real.log n := by
  admit

/-- Pair up elements of a list by multiplying consecutive pairs. -/
def pairProd : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | a :: b :: rest => (a * b) :: pairProd rest

/-- The product of a list equals the product of its paired version. -/
lemma pairProd_prod (l : List ℕ) : l.prod = (pairProd l).prod := by
  admit

/-- The length of the paired list is `⌈l.length / 2⌉ = (l.length + 1) / 2`. -/
lemma pairProd_length (l : List ℕ) : (pairProd l).length = (l.length + 1) / 2 := by
  admit

/-- If all elements of `l` are at most `n`, then all elements of `pairProd l` are at most `n²`. -/
lemma pairProd_bound (l : List ℕ) (n : ℕ) (hl : ∀ x ∈ l, x ≤ n) :
    ∀ x ∈ pairProd l, x ≤ n ^ 2 := by
  admit

/-- One can factorize $n!$ into at most $n/2 - n / 2\log n + o(n / \log n)$
  numbers of size at most $n^2$.-

PROVIDED SOLUTION:
Group the factorization arising in Theorem \ref{erdos-sol-1} into pairs, using
  Lemma \ref{balance-zero}.
-/
theorem Solution_2 (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ n in .atTop, ∃ (t : ℕ) (a : Fin t → ℕ), ∏ i, a i = n.factorial ∧ ∀ i, a i ≤ n ^ 2 ∧
        t ≤ (n / 2) - n / (2 * Real.log n) + ε * n / Real.log n := by
  admit

end Erdos392
