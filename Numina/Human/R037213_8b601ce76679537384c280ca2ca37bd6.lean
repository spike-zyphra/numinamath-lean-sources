import Mathlib

open Finset

/-How many times does 24 divide into 100 !?-/
theorem number_theory_610871 : multiplicity 24 (Nat.factorial 100) = 32 := by
-- Prepare to use padicValNat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
-- Prove two easy lemma
  have aux1 : Nat.log 2 100 = 6 := by rw [Nat.log_eq_iff]; all_goals norm_num
  have aux2 : Nat.log 3 100 = 4 := by rw [Nat.log_eq_iff]; all_goals norm_num
-- We need to show $24^32$ divides $100!$ but $24^33$ does not divide $100!$
  apply multiplicity_eq_of_dvd_of_not_dvd; rw [show 24 = 2^3*3 by simp, mul_pow]
  rw [← pow_mul, show 3*32 = 96 by simp]; apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
  · rw [Nat.coprime_pow_left_iff, Nat.coprime_pow_right_iff]; all_goals norm_num
  -- Prove that $2^96$ divides $100!$ by computing the padicValNat $2$ of $100!$
  · rw [padicValNat_dvd_iff]; right
    rw [padicValNat_factorial (show Nat.log 2 100 < 7 by simp [aux1])]
    simp [show Ico 1 7 = {1, 2, 3, 4, 5, 6} by decide]
  -- Prove that $3^32$ divides $100!$ by computing the padicValNat $3$ of $100!$
  · rw [padicValNat_dvd_iff]; right
    rw [padicValNat_factorial (show Nat.log 3 100 < 5 by simp [aux2])]
    simp [show Ico 1 5 = {1, 2, 3, 4} by decide]
-- Assume the contrary that $24^25$ divides $100!$, we derive a contradiction by computing padicValNat $2$
  rw [show 32+1 = 33 by simp, show 24 = 2^3*3 by simp, mul_pow]
  rw [← pow_mul, show 3*33 = 99 by simp]; intro h
  replace h : 2 ^ 99 ∣ Nat.factorial 100 := by apply dvd_trans _ h; apply dvd_mul_right
  rw [padicValNat_dvd_iff] at h; rcases h with _|h
  · have : 0 < Nat.factorial 100 := by positivity
    omega
  rw [padicValNat_factorial (show Nat.log 2 100 < 7 by simp [aux1])] at h
  simp [show Ico 1 7 = {1, 2, 3, 4, 5, 6} by decide] at h