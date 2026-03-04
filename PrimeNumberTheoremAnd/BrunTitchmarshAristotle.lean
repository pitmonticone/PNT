import Mathlib
import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.AsymptoticsAristotle
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.SelbergAristotle
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.SelbergBoundsAristotle

/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/


open Sieve SelbergSieve BoundingSieve
open Filter Asymptotics
open scoped Nat ArithmeticFunction BigOperators ArithmeticFunction.zeta ArithmeticFunction.omega

noncomputable section
namespace BrunTitchmarsh

/- Sifting primes ≤ z from the interval [x, x+y] -/
def primeInterSieve (x y z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := Finset.Icc (Nat.ceil x) (Nat.floor (x+y))
  prodPrimes := primorial (Nat.floor z)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := y
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by admit
  nu_pos_of_prime := fun p hp _ => by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := z
  one_le_level := hz

/- The number of primes in the interval [a, b] -/
def primesBetween (a b : ℝ) : ℕ :=
  (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter (Nat.Prime) |>.card

variable (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 ≤ z)

open Classical in
theorem siftedSum_eq_card :
    siftedSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) =
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
        (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  admit

open Classical in
theorem primesBetween_subset :
  (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter (Nat.Prime) ⊆
    (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d) ∪ (Finset.Icc 1 (Nat.floor z)) := by
  admit

theorem primesBetween_le_siftedSum_add :
    primesBetween x (x+y) ≤
      siftedSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) + z := by
  admit

section Remainder

theorem Ioc_filter_dvd_eq (d a b : ℕ) (hd : d ≠ 0) :
  Finset.filter (fun x => d ∣ x) (Finset.Ioc a b) =
    Finset.image (fun x => x * d) (Finset.Ioc (a / d) (b / d)) := by
  admit

theorem card_Ioc_filter_dvd (d a b : ℕ) (hd : d ≠ 0) :
    (Finset.filter (fun x => d ∣ x) (Finset.Ioc a b)).card = b / d - a / d := by
  admit

theorem multSum_eq (d : ℕ) (hd : d ≠ 0) :
    multSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) d =
      ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) := by
  admit

theorem rem_eq (d : ℕ) (hd : d ≠ 0) :
    rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d =
      ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) - (↑d)⁻¹ * y := by
  admit

theorem Nat.ceil_le_self_add_one (x : ℝ) (hx : 0 ≤ x) : Nat.ceil x ≤ x + 1 := by
  admit

theorem floor_approx (x : ℝ) (hx : 0 ≤ x) :
    ∃ C, |C| ≤ 1 ∧ ↑((Nat.floor x)) = x + C := by
  admit

theorem ceil_approx (x : ℝ) (hx : 0 ≤ x) : ∃ C, |C| ≤ 1 ∧ ↑((Nat.ceil x)) = x + C := by
  admit

theorem nat_div_approx (a b : ℕ) : ∃ C, |C| ≤ 1 ∧ ↑(a/b) = (a/b : ℝ) + C := by
  admit

theorem floor_div_approx (x : ℝ) (hx : 0 ≤ x) (d : ℕ) :
    ∃ C, |C| ≤ 2 ∧ ↑((Nat.floor x)/d) = x / d + C := by
  admit

theorem abs_rem_le {d : ℕ} (hd : d ≠ 0) :
    |rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d| ≤ 5 := by
  admit

end Remainder

theorem boudingSum_ge : (primeInterSieve x y z hz).selbergBoundingSum ≥ Real.log z / 2 := by
  admit

theorem primeSieve_rem_sum_le :
    ∑ d ∈ (primeInterSieve x y z hz).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then (3:ℝ) ^ ω d *
          |rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d| else 0)
      ≤ 5 * z * (1+Real.log z)^3 := by
  admit

theorem siftedSum_le (hz : 1 < z) :
    siftedSum (s := toBoundingSieve (self := primeInterSieve x y z (le_of_lt hz)))
      ≤ 2 * y / Real.log z + 5 * z * (1+Real.log z)^3  := by
  admit

theorem primesBetween_le (hz : 1 < z) :
    primesBetween x (x+y) ≤ 2 * y / Real.log z + 6 * z * (1+Real.log z)^3 := by
  admit

theorem primesBetween_one (n : ℕ) :
    primesBetween 1 n = ((Finset.range (n+1)).filter Nat.Prime).card := by
  admit

theorem primesBetween_mono_right (a b c : ℝ) (hbc : b ≤ c) :
    primesBetween a b ≤ primesBetween a c := by
  admit

theorem tmp (N : ℕ) :
    ((Finset.range N).filter Nat.Prime).card ≤
      4 * (N / Real.log N) + 6 * (N ^ (1/2 : ℝ) * (1 + 1/2 * Real.log N)^3) := by
  admit

theorem rpow_mul_rpow_log_isBigO_id_div_log (k : ℝ) {r : ℝ} (hr : r < 1) :
    (fun x ↦ (x : ℝ) ^ (r : ℝ) * (Real.log x)^k) =O[atTop]
      (fun x ↦ x / Real.log x) := by
  admit

theorem err_isBigO :
    (fun x ↦ (x ^ (1 / 2 : ℝ) * (1 + 1 / 2 * Real.log x) ^ 3)) =O[atTop]
      fun x ↦ (x / Real.log x) := by
  admit

theorem card_range_filter_prime_isBigO :
    (fun N ↦ ((Finset.range N).filter Nat.Prime).card : ℕ → ℝ) =O[atTop]
      (fun N ↦ N / Real.log N) := by
  admit

theorem prime_or_pow (N n : ℕ) (hnN : n < N) (hnprime : IsPrimePow n) :
    Nat.Prime n ∨ (∃ (m : ℕ), m < Real.sqrt N ∧ ∃ k ≤ Nat.log 2 N, n = m ^ k) := by
  admit

theorem range_filter_isPrimePow_subset_union (N : ℕ) :
    ((Finset.range N).filter IsPrimePow) ⊆ (Finset.range N).filter Nat.Prime ∪
      ((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ Finset.range (Nat.log 2 N + 1)).image
        (fun p ↦ p.1 ^ p.2) := by
  admit

theorem IsBigO.nat_Top_of_atTop (f g : ℕ → ℝ) (h : f =O[Filter.atTop] g)
    (h0 : ∀ n, g n = 0 → f n = 0) : f =O[⊤] g := by
  admit

theorem pows_small_primes_le (N : ℕ) :
    (((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ Finset.range (Nat.log 2 N + 1)).image
      (fun p ↦ p.1 ^ p.2)).card ≤
        (N : ℝ) ^ (1/2 : ℝ) * (1 + Real.log N / Real.log 2) := by
  admit

theorem one_add_log_div_log_two_isBigO :
    (fun N ↦ (1 + Real.log N / Real.log 2)) =O[atTop] (fun N ↦ Real.log N) := by
  admit

theorem pow_half_mul_one_add_log_div_isBigO :
    (fun N ↦ (N : ℝ) ^ (1/2 : ℝ) * (1 + Real.log N / Real.log 2)) =O[Filter.atTop]
      (fun N ↦ N / Real.log N) := by
  admit

theorem card_pows_aux :
    (fun N ↦ (((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ
      Finset.range (Nat.log 2 N + 1)).image (fun p ↦ p.1 ^ p.2)).card : ℕ → ℝ) =O[atTop]
        fun N ↦ N / Real.log N := by
  admit

theorem card_isPrimePow_isBigO :
    (fun N ↦ (((Finset.range N).filter IsPrimePow).card:ℝ)) =O[atTop]
      (fun N ↦ N / Real.log N) := by
  admit

theorem card_range_filter_isPrimePow_le :
    ∃ C, ∀ N, ((Finset.range N).filter IsPrimePow).card ≤ C * (N / Real.log N) := by
  admit

-- #print axioms card_isPrimePow_isBigO

end BrunTitchmarsh
