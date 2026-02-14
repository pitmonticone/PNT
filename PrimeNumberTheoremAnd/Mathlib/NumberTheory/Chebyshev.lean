/-
Copyright (c) 2025 Alastair Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Terry Tao, Ruben Van de Velde
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.VonMangoldt

import Mathlib.Data.Nat.Prime.Int

/-!
# Chebyshev functions

This file defines the Chebyshev functions `theta` and `psi`.
These give logarithmically weighted sums of primes and prime powers.

## Main definitions

- `Chebyshev.psi` gives the sum of `ArithmeticFunction.vonMangoldt`
- `Chebyshev.theta` gives the sum of `log p` over primes

## Main results

- `Chebyshev.theta_eq_log_primorial` shows that `θ x` is the log of the product of primes up to x
- `Chebyshev.theta_le_log4_mul_x` gives Chebyshev's upper bound on `θ`
- `Chebyshev.psi_eq_sum_theta` and `Chebyshev.psi_eq_theta_add_sum_theta` relate `psi` to `theta`.
- `Chevyshev.psi_le_const_mul_self` gives Chebyshev's upper bound on `ψ`.

## Notation

We introduce the scoped notations `θ` and `ψ` in the Chebyshev namespace for the Chebyshev
functions.

## References

Parts of this file were upstreamed from the PrimeNumberTheoremAnd project by Kontorovich et al, https://github.com/alexKontorovich/PrimeNumberTheoremAnd.

## TODOS

- Upstream the results relating `theta` and `psi` to the prime counting function.
- Prove Chebyshev's lower bound.
-/
@[expose] public section

open Nat hiding log
open Finset Real
open ArithmeticFunction hiding log

namespace Chebyshev

/-- The sum of `ArithmeticFunction.vonMangoldt` over integers `n ≤ x`. -/
noncomputable def psi (x : ℝ) : ℝ :=
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n

@[inherit_doc]
scoped notation "ψ" => Chebyshev.psi

/-- The sum of `log p` over primes `p ≤ x`. -/
noncomputable def theta (x : ℝ) : ℝ :=
    ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p

@[inherit_doc]
scoped notation "θ" => Chebyshev.theta

theorem psi_nonneg (x : ℝ) : 0 ≤ ψ x :=
  sum_nonneg fun _ _ ↦ (by simp)

theorem theta_nonneg (x : ℝ) : 0 ≤ θ x :=
  sum_nonneg fun n hn ↦ log_nonneg (by aesop)

theorem psi_eq_sum_Icc (x : ℝ) :
    ψ x = ∑ n ∈ Icc 0 ⌊x⌋₊, Λ n := by
  rw [psi, ← add_sum_Ioc_eq_sum_Icc] <;> simp

theorem theta_eq_sum_Icc (x : ℝ) :
    θ x = ∑ p ∈ Icc 0 ⌊x⌋₊ with p.Prime, log p := by
  rw [theta, sum_filter, sum_filter, ← add_sum_Ioc_eq_sum_Icc] <;> simp

theorem psi_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : ψ x = 0 := by
  apply sum_eq_zero fun n hn ↦ ?_
  simp only [mem_Ioc] at hn
  convert vonMangoldt_apply_one
  have := lt_of_le_of_lt (le_floor_iff' hn.1.ne.symm |>.mp hn.2) hx
  norm_cast at this
  linarith

theorem theta_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : θ x = 0 := by
  apply sum_eq_zero fun n hn ↦ ?_
  convert log_one
  simp only [mem_filter, mem_Ioc] at hn
  have := lt_of_le_of_lt (le_floor_iff' hn.1.1.ne.symm |>.mp hn.1.2) hx
  norm_cast at ⊢ this
  linarith

theorem psi_eq_psi_coe_floor (x : ℝ) : ψ x = ψ ⌊x⌋₊ := by
  unfold psi
  rw [floor_natCast]

theorem theta_eq_theta_coe_floor (x : ℝ) : θ x = θ ⌊x⌋₊ := by
  unfold theta
  rw [floor_natCast]

theorem psi_mono : Monotone ψ := by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg
  · exact Ioc_subset_Ioc (by rfl) <| floor_le_floor hxy
  · simp

theorem theta_mono : Monotone θ := by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg
  · exact filter_subset_filter _ <| Ioc_subset_Ioc_right <| floor_mono hxy
  · simp only [mem_filter]
    exact fun p hp _ ↦ log_nonneg (mod_cast hp.2.one_le)

/-- `θ x` is the log of the product of the primes up to `x`. -/
theorem theta_eq_log_primorial (x : ℝ) : θ x = log (primorial ⌊x⌋₊) := by admit

/-- Chebyshev's upper bound: `θ x ≤ c x` with the constant `c = log 4`. -/
theorem theta_le_log4_mul_x {x : ℝ} (hx : 0 ≤ x) : θ x ≤ log 4 * x := by
  rw [theta_eq_log_primorial]
  trans log (4 ^ ⌊x⌋₊)
  · apply log_le_log <;> norm_cast
    exacts [primorial_pos _, primorial_le_4_pow _]
  rw [Real.log_pow, mul_comm]
  gcongr
  exact floor_le hx

/-!
## Relating `ψ` and `θ`

We isolate the contributions of different prime powers to `ψ` and use this to show that `ψ` and `θ`
are close.
-/

/-- A sum over prime powers may be written as a double sum over exponents and then primes. -/
theorem sum_PrimePow_eq_sum_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R) {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊ with IsPrimePow n, f n
      = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime, f (p ^ k) := by
  admit

theorem psi_eq_sum_theta {x : ℝ} (hx : 0 ≤ x) :
    ψ x = ∑ n ∈ Icc 1 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / n)) := by
  simp_rw [psi, vonMangoldt_apply, ← sum_filter, sum_PrimePow_eq_sum_sum _ hx]
  apply sum_congr rfl fun _ hk ↦ sum_congr rfl fun _ _ ↦ ?_
  rw [Nat.Prime.pow_minFac _ (by linarith [mem_Icc.mp hk])]
  simp_all

theorem psi_eq_theta_add_sum_theta {x : ℝ} (hx : 2 ≤ x) :
    ψ x = θ x + ∑ n ∈ Icc 2 ⌊log x / log 2⌋₊, θ (x ^ ((1 : ℝ) / n)) := by
  rw [psi_eq_sum_theta (by linarith), ← add_sum_Ioc_eq_sum_Icc]
  · congr
    simp
  · rw [le_floor_iff' one_ne_zero, le_div_iff₀ (by positivity), cast_one, one_mul]
    gcongr

theorem theta_le_psi (x : ℝ) : θ x ≤ ψ x := by
  admit

--Note that a more careful argument could remove the log x in the following with a worse constant.
/-- `|ψ x - θ x| ≤ c x √ x` with an explicit constant c. -/
theorem abs_psi_sub_theta_le_sqrt_mul_log {x : ℝ} (hx : 1 ≤ x) :
    |ψ x - θ x| ≤ 2 * x.sqrt * x.log := by
  admit

/-- Explicit upper bound on `ψ`. -/
theorem psi_le {x : ℝ} (hx : 1 ≤ x) :
    ψ x ≤ log 4 * x + 2 * x.sqrt * x.log := by
  calc
  _ = ψ x - θ x + θ x := by ring
  _ ≤ 2 * x.sqrt * x.log + log 4 * x := by
    gcongr
    · exact le_trans (le_abs_self _) (abs_psi_sub_theta_le_sqrt_mul_log hx)
    · exact theta_le_log4_mul_x (by linarith)
  _ = _ := by ring

/- Chebyshev's bound `ψ x ≤ c x` with an explicit constant.
Note that `Chebyshev.psi_le` gives a sharper bound with a better main term. -/
theorem psi_le_const_mul_self {x : ℝ} (hx : 0 ≤ x) :
    ψ x ≤ (log 4 + 4) * x := by
  admit

/-- `ψ - θ` is the sum of `Λ` over non-primes. -/
theorem psi_sub_theta_eq_sum_not_prime (x : ℝ) :
    ψ x - θ x = ∑ n ∈ Ioc 0 ⌊x⌋₊ with ¬n.Prime, vonMangoldt n := by
  rw [psi, theta, sum_filter, sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun n hn ↦ ?_
  split_ifs with h
  · simp [h, vonMangoldt_apply_prime]
  · simp

end Chebyshev
