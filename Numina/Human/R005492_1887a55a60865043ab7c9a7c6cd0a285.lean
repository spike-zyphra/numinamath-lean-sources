import Mathlib

open Finset Real Nat

/-Let s(n) denote the number of 1's in the binary representation of n.
Compute (1/255) * ∑ n ∈ range 16, 2^n * (-1)^(s n) -/

-- Define s(n) as the number of 1's in the binary representation of n
def s (n : ℕ) : ℕ := (digits 2 n).count 1

theorem number_theory_608487: ((1: ℚ) / 255) * ∑ n ∈ range 16, 2 ^ n * (-1) ^ (s n) = 45 := by

    have h0 : (2: ℚ) ^ 0 * (-1) ^ (s 0) = 1 := by simp [s]
    have h1 :  (2: ℚ) ^ 1 * (-1) ^ (s 1) = -2 := by simp [s]
    have h2 :  (2: ℚ) ^ 2 * (-1) ^ (s 2) = -4 := by simp [s]; norm_num
    have h3 :  (2: ℚ) ^ 3 * (-1) ^ (s 3) = 8 := by simp [s]; norm_num
    have h4 :  (2: ℚ) ^ 4 * (-1) ^ (s 4) = -16 := by simp [s]; norm_num
    have h5 :  (2: ℚ) ^ 5 * (-1) ^ (s 5) = 32 := by simp [s]; norm_num
    have h6 :  (2: ℚ) ^ 6 * (-1) ^ (s 6) = 64 := by simp [s]; norm_num
    have h7 :  (2: ℚ) ^ 7 * (-1) ^ (s 7) = -128 := by simp [s]; norm_num
    have h8 :  (2: ℚ) ^ 8 * (-1) ^ (s 8) = -256 := by simp [s]; norm_num
    have h9 :   (2: ℚ) ^ 9 * (-1) ^ (s 9) = 512 := by simp [s]; norm_num
    have h10 :  (2: ℚ) ^ 10 * (-1) ^ (s 10) = 1024 := by simp [s]; norm_num
    have h11 :  (2: ℚ) ^ 11 * (-1) ^ (s 11) = -2048 := by simp [s]; norm_num
    have h12 :  (2: ℚ) ^ 12 * (-1) ^ (s 12) = 4096 := by simp [s]; norm_num
    have h13 :  (2: ℚ) ^ 13 * (-1) ^ (s 13) = -8192 := by simp [s]; norm_num
    have h14 :  (2: ℚ) ^ 14 * (-1) ^ (s 14) = -16384 := by simp [s]; norm_num
    have h15 :  (2: ℚ) ^ 15 * (-1) ^ (s 15) = 32768 := by simp [s]; norm_num

    -- Sum all the terms
    simp only [sum_range_succ]
    rw [h0, h1, h2, h3,h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
    field_simp
    ring