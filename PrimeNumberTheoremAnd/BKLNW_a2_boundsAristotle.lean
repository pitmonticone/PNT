import Mathlib
import PrimeNumberTheoremAnd.BKLNWAristotle

/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/

/-!
# BKLNW a₂ Glue Proofs (Corollary 5.1 Remark)

Connects `a₂(b) = (1+α) * max(f(exp b), f(2^(⌊b/log2⌋₊+1)))` to certified bounds.
Proves `cor_5_1_rem` from PrimeNumberTheoremAnd.BKLNW.

Uses:
- `f` and `a₂` from PrimeNumberTheoremAnd.BKLNW
- Numerical certificates from LeanCert.Examples.BKLNW_a2_bounds and LeanCert.Examples.BKLNW_a2_pow2
- `interval_decide` tactic from LeanCert
-/

open Real BKLNW

-- Note: Don't open LeanCert.Examples.BKLNW_a2_pow2 to avoid `f` ambiguity with BKLNW.f

-- Connect PNT+'s f with LeanCert's f (definitionally equal)
private lemma f_eq_leancert_f : BKLNW.f = LeanCert.Examples.BKLNW_a2_pow2.f := by
  admit

-- Convert rpow with negative nat exponent to division
private lemma rpow_neg_nat (n : ℕ) : (10:ℝ) ^ (-(↑n : ℝ)) = (1:ℝ) / 10 ^ n := by
  admit

-- ═══════════════════════ α connection ═══════════════════════

private lemma alpha_eq : Inputs.default.α = 193571378 / (10:ℝ)^16 := by
  admit

-- ═══════════════════════ b = 20 ═══════════════════════
private lemma floor_20 : ⌊(20 : ℝ) / log 2⌋₊ = 28 := by
  admit

private lemma a2_20_exp_lower :
    (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (20:ℝ)) := by
  admit

private lemma a2_20_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (20:ℝ)) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  admit

private lemma cert_pow29_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(29:ℕ)) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  admit

private lemma a2_20_lower :
    (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 20)) (f ((2:ℝ)^(⌊(20:ℝ)/log 2⌋₊ + 1))) := by
  admit

private lemma a2_20_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 20)) (f ((2:ℝ)^(⌊(20:ℝ)/log 2⌋₊ + 1))) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  admit

theorem a2_20_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 20)) (f ((2:ℝ)^(⌊(20:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.4262 : ℝ) ((1.4262 : ℝ) + (1:ℝ) / 10^4) := by
  admit

-- ═══════════════════════ b = 25 ═══════════════════════
private lemma floor_25 : ⌊(25 : ℝ) / log 2⌋₊ = 36 := by
  admit

private lemma a2_25_exp_lower :
    (1.2195 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (25:ℝ)) := by
  admit

private lemma a2_25_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (25:ℝ)) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by
  admit

private lemma cert_pow37_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(37:ℕ)) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by
  admit

private lemma a2_25_lower :
    (1.2195 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 25)) (f ((2:ℝ)^(⌊(25:ℝ)/log 2⌋₊ + 1))) := by
  admit

private lemma a2_25_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 25)) (f ((2:ℝ)^(⌊(25:ℝ)/log 2⌋₊ + 1))) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by
  admit

theorem a2_25_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 25)) (f ((2:ℝ)^(⌊(25:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.2195 : ℝ) ((1.2195 : ℝ) + (1:ℝ) / 10^4) := by
  admit

-- ═══════════════════════ b = 30 ═══════════════════════
private lemma floor_30 : ⌊(30 : ℝ) / log 2⌋₊ = 43 := by
  admit

private lemma a2_30_exp_lower :
    (1.1210 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (30:ℝ)) := by
  admit

private lemma a2_30_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (30:ℝ)) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 := by
  admit

private lemma cert_pow44_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(44:ℕ)) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 := by
  admit

private lemma a2_30_lower :
    (1.1210 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 30)) (f ((2:ℝ)^(⌊(30:ℝ)/log 2⌋₊ + 1))) := by
  admit

private lemma a2_30_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 30)) (f ((2:ℝ)^(⌊(30:ℝ)/log 2⌋₊ + 1))) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 := by
  admit

theorem a2_30_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 30)) (f ((2:ℝ)^(⌊(30:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.1210 : ℝ) ((1.1210 : ℝ) + (1:ℝ) / 10^4) := by
  admit

-- ═══════════════════════ b = 35 ═══════════════════════
private lemma floor_35 : ⌊(35 : ℝ) / log 2⌋₊ = 50 := by
  admit

private lemma a2_35_exp_lower :
    (1.07086 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (35:ℝ)) := by
  admit

private lemma a2_35_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (35:ℝ)) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 := by
  admit

private lemma cert_pow51_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(51:ℕ)) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 := by
  admit

private lemma a2_35_lower :
    (1.07086 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 35)) (f ((2:ℝ)^(⌊(35:ℝ)/log 2⌋₊ + 1))) := by
  admit

private lemma a2_35_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 35)) (f ((2:ℝ)^(⌊(35:ℝ)/log 2⌋₊ + 1))) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 := by
  admit

theorem a2_35_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 35)) (f ((2:ℝ)^(⌊(35:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.07086 : ℝ) ((1.07086 : ℝ) + (1:ℝ) / 10^5) := by
  admit

-- ═══════════════════════ b = 40 ═══════════════════════
private lemma floor_40 : ⌊(40 : ℝ) / log 2⌋₊ = 57 := by
  admit

private lemma a2_40_exp_lower :
    (1.04319 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (40:ℝ)) := by
  admit

private lemma a2_40_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (40:ℝ)) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 := by
  admit

private lemma cert_pow58_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(58:ℕ)) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 := by
  admit

private lemma a2_40_lower :
    (1.04319 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 40)) (f ((2:ℝ)^(⌊(40:ℝ)/log 2⌋₊ + 1))) := by
  admit

private lemma a2_40_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 40)) (f ((2:ℝ)^(⌊(40:ℝ)/log 2⌋₊ + 1))) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 := by
  admit

theorem a2_40_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 40)) (f ((2:ℝ)^(⌊(40:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.04319 : ℝ) ((1.04319 : ℝ) + (1:ℝ) / 10^5) := by
  admit

-- ═══════════════════════ b = 43 ═══════════════════════
private lemma floor_43 : ⌊(43 : ℝ) / log 2⌋₊ = 62 := by
  admit

private lemma a2_43_exp_lower :
    (1.03252 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (43:ℝ)) := by
  admit

private lemma a2_43_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (43:ℝ)) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 := by
  admit

private lemma cert_pow63_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(63:ℕ)) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 := by
  admit

private lemma a2_43_lower :
    (1.03252 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 43)) (f ((2:ℝ)^(⌊(43:ℝ)/log 2⌋₊ + 1))) := by
  admit

private lemma a2_43_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 43)) (f ((2:ℝ)^(⌊(43:ℝ)/log 2⌋₊ + 1))) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 := by
  admit

theorem a2_43_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 43)) (f ((2:ℝ)^(⌊(43:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.03252 : ℝ) ((1.03252 : ℝ) + (1:ℝ) / 10^5) := by
  admit

-- ═══════════════════════ b = 100 ═══════════════════════
private lemma floor_100 : ⌊(100 : ℝ) / log 2⌋₊ = 144 := by
  admit

private lemma a2_100_exp_lower :
    (1.0002420 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (100:ℝ)) := by
  admit

private lemma a2_100_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (100:ℝ)) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by
  admit

private lemma cert_pow145_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(145:ℕ)) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by
  admit

private lemma a2_100_lower :
    (1.0002420 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 100)) (f ((2:ℝ)^(⌊(100:ℝ)/log 2⌋₊ + 1))) := by
  admit

private lemma a2_100_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 100)) (f ((2:ℝ)^(⌊(100:ℝ)/log 2⌋₊ + 1))) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by
  admit

theorem a2_100_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 100)) (f ((2:ℝ)^(⌊(100:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.0002420 : ℝ) ((1.0002420 : ℝ) + (1:ℝ) / 10^7) := by
  admit

-- ═══════════════════════ b = 150 ═══════════════════════
private lemma floor_150 : ⌊(150 : ℝ) / log 2⌋₊ = 216 := by
  admit

private lemma a2_150_exp_lower :
    (1.000003748 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (150:ℝ)) := by
  admit

private lemma a2_150_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (150:ℝ)) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by
  admit

private lemma cert_pow217_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(217:ℕ)) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by
  admit

private lemma a2_150_lower :
    (1.000003748 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 150)) (f ((2:ℝ)^(⌊(150:ℝ)/log 2⌋₊ + 1))) := by
  admit

private lemma a2_150_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 150)) (f ((2:ℝ)^(⌊(150:ℝ)/log 2⌋₊ + 1))) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by
  admit

theorem a2_150_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 150)) (f ((2:ℝ)^(⌊(150:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.000003748 : ℝ) ((1.000003748 : ℝ) + (1:ℝ) / 10^8) := by
  admit

-- ═══════════════════════ b = 200 ═══════════════════════
private lemma floor_200 : ⌊(200 : ℝ) / log 2⌋₊ = 288 := by
  admit

private lemma a2_200_exp_lower :
    (1.00000007713 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (200:ℝ)) := by
  admit

private lemma a2_200_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (200:ℝ)) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by
  admit

private lemma cert_pow289_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(289:ℕ)) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by
  admit

private lemma a2_200_lower :
    (1.00000007713 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 200)) (f ((2:ℝ)^(⌊(200:ℝ)/log 2⌋₊ + 1))) := by
  admit

private lemma a2_200_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 200)) (f ((2:ℝ)^(⌊(200:ℝ)/log 2⌋₊ + 1))) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by
  admit

theorem a2_200_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 200)) (f ((2:ℝ)^(⌊(200:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.00000007713 : ℝ) ((1.00000007713 : ℝ) + (1:ℝ) / 10^9) := by
  admit

-- ═══════════════════════ b = 250 ═══════════════════════
private lemma floor_250 : ⌊(250 : ℝ) / log 2⌋₊ = 360 := by
  admit

private lemma a2_250_exp_lower :
    (1.00000002025 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (250:ℝ)) := by
  admit

private lemma a2_250_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (250:ℝ)) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by
  admit

private lemma cert_pow361_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(361:ℕ)) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by
  admit

private lemma a2_250_lower :
    (1.00000002025 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 250)) (f ((2:ℝ)^(⌊(250:ℝ)/log 2⌋₊ + 1))) := by
  admit

private lemma a2_250_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 250)) (f ((2:ℝ)^(⌊(250:ℝ)/log 2⌋₊ + 1))) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by
  admit

theorem a2_250_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 250)) (f ((2:ℝ)^(⌊(250:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.00000002025 : ℝ) ((1.00000002025 : ℝ) + (1:ℝ) / 10^9) := by
  admit

-- ═══════════════════════ b = 300 ═══════════════════════
private lemma floor_300 : ⌊(300 : ℝ) / log 2⌋₊ = 432 := by
  admit

private lemma a2_300_exp_lower :
    (1.00000001937 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (300:ℝ)) := by
  admit

private lemma a2_300_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (300:ℝ)) ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^9 := by
  admit

private lemma cert_pow433_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(433:ℕ)) ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^8 := by
  admit

private lemma a2_300_lower :
    (1.00000001937 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 300)) (f ((2:ℝ)^(⌊(300:ℝ)/log 2⌋₊ + 1))) := by
  admit

private lemma a2_300_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 300)) (f ((2:ℝ)^(⌊(300:ℝ)/log 2⌋₊ + 1))) ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^8 := by
  admit

theorem a2_300_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 300)) (f ((2:ℝ)^(⌊(300:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.00000001937 : ℝ) ((1.00000001937 : ℝ) + (1:ℝ) / 10^8) := by
  admit

-- ═══════════════════════ Main Theorem ═══════════════════════

theorem cor_5_1_rem' (b a₂b : ℝ) (m : ℕ) (hb : (b, a₂b, m) ∈ table_cor_5_1) :
    a₂ b ∈ Set.Icc a₂b (a₂b + 10^(-m:ℝ)) := by
  admit

-- Canonical theorem (replaces the sorry in BKLNW.lean)
/-- **Remark after BKLNW Corollary 5.1**

We have the following values for $a_2$, given by the table after [reference].
-/
theorem BKLNW.cor_5_1_rem (b a₂b : ℝ) (m : ℕ) (hb : (b, a₂b, m) ∈ table_cor_5_1) :
    a₂ b ∈ Set.Icc a₂b (a₂b + 10^(-m:ℝ)) := by
  admit