import Mathlib

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset


namespace ArithmeticFunction.IsMultiplicative

variable {R : Type*}

theorem prod_factors_of_mult (f : ArithmeticFunction ℝ)
    (h_mult : ArithmeticFunction.IsMultiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ a ∈ l.primeFactors, f a = f l := by
  admit

end ArithmeticFunction.IsMultiplicative

namespace Aux
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 := by
  admit

theorem ite_sum_zero {p : Prop} [Decidable p] (s : Finset ℕ) (f : ℕ → ℝ) :
    (if p then (∑ x ∈ s, f x) else 0) = ∑ x ∈ s, if p then f x else 0 := by
  admit

theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors,
        ∑ d1 ∈ d.divisors,
          ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d ∈ n.divisors,
        ∑ d1 ∈ n.divisors,
          ∑ d2 ∈ n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 := by
  admit

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (moebius d:ℤ) else 0) = if l = m then (moebius l:ℤ) else 0 := by
  admit

theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then moebius d else 0) = if l = m then moebius l else 0 := by
  admit

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (moebius d : ℝ) else 0) =
      if l = m then (moebius l : ℝ) else 0 := by
  admit

theorem multiplicative_zero_of_zero_dvd (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    {m n : ℕ} (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 := by
  admit

theorem div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    (l d : ℕ) (hdl : d ∣ l) (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) := by
  admit

theorem inv_sub_antitoneOn_gt
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (c : R) :
    AntitoneOn (fun x:R ↦ (x-c)⁻¹) (Set.Ioi c) := by
  admit

theorem inv_sub_antitoneOn_Icc
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  admit

theorem inv_antitoneOn_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    AntitoneOn (fun x:R ↦ x⁻¹) (Set.Ioi 0) := by
  admit

theorem inv_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) (ha : 0 < a) :
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  admit

theorem log_add_one_le_sum_inv (n : ℕ) :
    Real.log ↑(n+1) ≤ ∑ d ∈ Finset.Icc 1 n, (d:ℝ)⁻¹ := by
  admit

theorem log_le_sum_inv (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ := by
  admit

theorem sum_inv_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log ↑n := by
  admit

theorem sum_inv_le_log_real (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ ≤ 1 + Real.log y := by
  admit

-- Lemma 3.1 in Heath-Brown's notes
theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if d ≤ x then (k:ℝ) ^ (ω d) / (d : ℝ) else (0 : ℝ))
    ≤ (1 + Real.log x) ^ k := by
  admit

theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤
      x * (1 + Real.log x) ^ h := by
  admit

end Aux
