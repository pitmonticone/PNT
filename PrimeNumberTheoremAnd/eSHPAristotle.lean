import Mathlib
import PrimeNumberTheoremAnd.DefsAristotle
import PrimeNumberTheoremAnd.eSHP_tablesAristotle

open Nat

/-!
# Prime gap data from eSHP

Numerical results on prime gaps from [reference].
-/

namespace eSHP
/-- **Table 8 prime gap record - unit test**

For every pair $(p_k,g_k)$ in Table 8 with $p_k < 30$, $g_k$ is the prime gap $p_{k+1} - p_k$, and all prime gaps preceding this gap are less than $g_k$.

PROVIDED SOLUTION:
Direct computation.
-/
theorem table_8_prime_gap_test (p g : ℕ) (h : (p, g) ∈ table_8) (htest : p < 30) : prime_gap_record p g := by
  admit

/-- **Table 8 prime gap records**

For every pair $(p_k,g_k)$ in Table 8, $g_k$ is the prime gap $p_{k+1} - p_k$, and all prime gaps preceding this gap are less than $g_k$.

PROVIDED SOLUTION:
Verified by computer.  Unlikely to be formalizable in Lean with current technology, except for the small values of the table.
-/
theorem table_8_prime_gap (p g : ℕ) (h : (p, g) ∈ table_8) : prime_gap_record p g := by
  sorry

/-- **Table 8 prime gap records - completeness unit test**

Table 8 contains ALL the prime gap records $(p_k,g_k)$ with $p_k \leq 30$.

PROVIDED SOLUTION:
Brute force verification.
-/
theorem table_8_prime_gap_complete_test (p g : ℕ) (hp : p ≤ 30)
    (hrecord : prime_gap_record p g) : (p, g) ∈ table_8 := by
  admit

/-- **Table 8 prime gap records - completeness**

Table 8 contains ALL the prime gap records $(p_k,g_k)$ with $p_k \leq 4 \times 10^{18}$.

PROVIDED SOLUTION:
Verified by computer.  Unlikely to be formalizable in Lean with current technology, except for the small values of the table.
-/
theorem table_8_prime_gap_complete (p g : ℕ) (hp : p ≤ 4 * 10 ^ 18) (hrecord : prime_gap_record p g) : (p, g) ∈ table_8 := by sorry


lemma exists_prime_gap_record_le (n : ℕ) :
    ∃ m, nth_prime m ≤ nth_prime n ∧ nth_prime_gap n ≤ nth_prime_gap m ∧
      prime_gap_record (nth_prime m) (nth_prime_gap m) := by
  admit

/-- **Maximum prime gap**

The maximum prime gap for primes less than or equal to $4 \times 10^{18}$ is $1476$.

PROVIDED SOLUTION:
If not, then there would be an entry in Table 8 with $g > 1476$, which can be verified not to be the case.
-/
theorem max_prime_gap (n : ℕ) (hp : nth_prime n ≤ 4 * 10 ^ 18) : nth_prime_gap n ≤ 1476 := by
  admit

/-- **Table 9 prime gaps - unit test**

For every pair $(g,P)$ in Table 9 with $P < 30$, $P$ is the first prime producing the prime gap $g$, and all smaller $g'$ (that are even or $1$) have a smaller first prime.

PROVIDED SOLUTION:
Direct computation.
-/
theorem table_9_prime_gap_test (g P : ℕ) (h : (g, P) ∈ table_9) (htest : P < 30) : first_gap_record g P := by
  admit

/-- **Table 9 prime gaps**

For every pair $(g,P)$ in Table 9, $P$ is the first prime producing the prime gap $g$, and all smaller $g'$ (that are even or $1$) have a smaller first prime.

PROVIDED SOLUTION:
Verified by computer.  Unlikely to be formalizable in Lean with current technology, except for the small values of the table.
-/
theorem table_9_prime_gap (g P : ℕ) (h : (g, P) ∈ table_9) : first_gap_record g P := by
  sorry


/-- Values of the first `9` primes (`0`-indexed). -/
lemma nth_prime_vals :
    nth_prime 0 = 2 ∧ nth_prime 1 = 3 ∧ nth_prime 2 = 5 ∧ nth_prime 3 = 7 ∧
    nth_prime 4 = 11 ∧ nth_prime 5 = 13 ∧ nth_prime 6 = 17 ∧ nth_prime 7 = 19 ∧
    nth_prime 8 = 23 := by
  admit

/-- For any odd number `g > 1`, the first prime gap of size `g` is `0` (meaning it doesn't exist). -/
lemma first_gap_odd_gt_1 {g : ℕ} (hg : Odd g) (hg1 : 1 < g) : first_gap g = 0 := by
  admit

/-- The first prime gap of size `1` occurs at prime `2`. -/
lemma first_gap_1 : first_gap 1 = 2 := by
  admit

/-- The first prime gap of size `2` occurs at prime `3`. -/
lemma first_gap_2 : first_gap 2 = 3 := by
  admit

/-- The first prime gap of size `3` does not occur. -/
lemma first_gap_3 : first_gap 3 = 0 := by
  admit

/-- The first prime gap of size `4` occurs at prime `7`. -/
lemma first_gap_4 : first_gap 4 = 7 := by
  admit

/-- The first prime gap of size `5` does not occur. -/
lemma first_gap_5 : first_gap 5 = 0 := by
  admit

/-- The first prime gap of size `6` occurs at prime `23`. -/
lemma first_gap_6 : first_gap 6 = 23 := by
  admit

/-- The first prime gap of size `7` does not occur. -/
lemma first_gap_7 : first_gap 7 = 0 := by
  admit

/-- **Table 9 prime gaps - completeness test**

Table 9 contains all first gap records $(g,P)$ with $g < 8$.

PROVIDED SOLUTION:
Brute force verification.
-/

theorem table_9_prime_gap_complete_test (g P : ℕ) (hg : g < 8) (hg' : 0 < g)
    (hrecord : first_gap_record g P) : (g, P) ∈ table_9 := by
  admit

/-- **Table 9 prime gaps - completeness**

Table 9 contains all first gap records $(g,P)$ with $g < 1346$

PROVIDED SOLUTION:
Verified by computer.  Unlikely to be formalizable in Lean with current technology, except for the small values of the table.
-/
theorem table_9_prime_gap_complete (g P : ℕ) (hg : g < 1346) (hg' : 0 < g) (hrecord : first_gap_record g P) : (g, P) ∈ table_9 := by
  sorry

/-- **Existence of prime gap**

Every gap $g < 1346$ that is even or one occurs as a prime gap with first prime at most $3278018069102480227$.

PROVIDED SOLUTION:
If not, then there would be an entry in Table 8 with $P > 3278018069102480227$, which can be verified not to be the case.
-/
theorem exists_prime_gap (g : ℕ) (hg : g ∈ Set.Ico 1 1476) (hg' : Even g ∨ g = 1) : first_gap g ≤ 3278018069102480227 := by
  sorry


end eSHP
