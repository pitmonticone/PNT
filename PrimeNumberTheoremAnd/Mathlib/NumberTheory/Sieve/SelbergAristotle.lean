import Mathlib
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.BasicAristotle

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/

/-!
# The Selberg Sieve

This file proves `selberg_bound_simple`, the main theorem of the Selberg.
-/

set_option lang.lemmaCmd true

noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve
set_option quotPrecheck false

variable (s : SelbergSieve)
local notation3 "ν" => BoundingSieve.nu (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "P" => BoundingSieve.prodPrimes (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "a" => BoundingSieve.weights (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "X" => BoundingSieve.totalMass (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "A" => BoundingSieve.support (self := SelbergSieve.toBoundingSieve (self := s))
local notation3 "𝒜" => BoundingSieve.multSum (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "R" => BoundingSieve.rem (s := SelbergSieve.toBoundingSieve (self := s))
local notation3 "g" => SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))
local notation3 "y" => SelbergSieve.level (self := s)
local notation3 "hy" => SelbergSieve.one_le_level (self := s)

@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors P, if l ^ 2 ≤ y then g l else 0

set_option quotPrecheck false
local notation3 "S" => SelbergSieve.selbergBoundingSum s

theorem selbergBoundingSum_pos :
    0 < S := by
  admit

theorem selbergBoundingSum_ne_zero : S ≠ 0 := by
  admit

theorem selbergBoundingSum_nonneg : 0 ≤ S := by
  admit

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ P then
    (ν d)⁻¹ * g d * μ d * S⁻¹ *
      ∑ m ∈ divisors P, if (d * m) ^ 2 ≤ y ∧ m.Coprime d then g m else 0
  else 0

-- This notation traditionally uses λ, which is unavailable in lean
set_option quotPrecheck false
local notation3 "γ" => SelbergSieve.selbergWeights s

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ P) :
    γ d = 0 := by
  admit

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ y) :
    γ d = 0 := by
  admit

@[aesop safe]
theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ P) :
    0 ≤ γ d * μ d := by
  admit

lemma sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  admit

--Important facts about the selberg weights
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    ν d * γ d =
      S⁻¹ * μ d *
        ∑ l ∈ divisors P, if d ∣ l ∧ l ^ 2 ≤ y then g l else 0 := by
  admit

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors P) :
    (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) =
      if l ^ 2 ≤ y then g l * μ l * S⁻¹ else 0 := by
  admit

def selbergMuPlus : ℕ → ℝ :=
  lambdaSquared γ

set_option quotPrecheck false
local notation3 "μ⁺" => SelbergSieve.selbergMuPlus s

theorem weight_one_of_selberg : γ 1 = 1 := by
  admit

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ y) : μ⁺ d = 0 := by
  admit

def selbergUbSieve : UpperBoundSieve :=
  ⟨μ⁺, upperMoebius_of_lambda_sq γ (s.weight_one_of_selberg)⟩

-- proved for general lambda squared sieves
theorem mainSum_eq_diag_quad_form :
    mainSum (s := s.toBoundingSieve) μ⁺ =
      ∑ l ∈ divisors P,
        1 / g l *
          (∑ d ∈ divisors P, if l ∣ d then ν d * γ d else 0) ^ 2 := by
  admit

theorem selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) μ⁺ = S⁻¹ := by
  admit

lemma eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  admit

private lemma _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors P) (hm : m ∈ divisors P) :
    k * m ∣ P ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ y ↔
    (k * m) ^ 2 ≤ y ∧ Coprime m d := by
  admit

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ P) :
    S ≥ γ d * ↑(μ d) * S := by
  admit

theorem selberg_bound_weights (d : ℕ) : |γ d| ≤ 1 := by
  admit

theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors P) :
    |μ⁺ n| ≤ (3:ℝ) ^ ω n := by
  admit

theorem selberg_bound_simple_errSum :
    errSum (s := s.toBoundingSieve) μ⁺ ≤
      ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  admit

theorem selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      X / S +
        ∑ d ∈ divisors P, if (d : ℝ) ≤ y then (3:ℝ) ^ ω d * |R d| else 0 := by
  admit

end SelbergSieve
