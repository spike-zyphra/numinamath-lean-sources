import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_110574 (x y : ℝ) : sqrt (4 * x ^ 2 - 12 * x + 25) + sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) ≤ 12 ↔ (x = 3 / 2 ∧ y = -1) := by
  constructor
  · -- Assume the inequality holds, prove (x = 3 / 2 ∧ y = -1)
    intro h
    have h1 : 0 ≤ 4 * x ^ 2 - 12 * x + 25 := by 
      nlinarith [sq_nonneg (x - 3 / 2)]
    have h2 : 0 ≤ 4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64 := by 
      nlinarith [sq_nonneg (2 * x + 3 * y)]
    have h3 : sqrt (4 * x ^ 2 - 12 * x + 25) ≥ 4 := by 
      have h4 : (4 * x ^ 2 - 12 * x + 25 : ℝ) ≥ 16 := by
        nlinarith [sq_nonneg (x - 3 / 2)]
      have h5 : sqrt (4 * x ^ 2 - 12 * x + 25) ≥ sqrt (16 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h6 : sqrt (16 : ℝ) = (4 : ℝ) := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith [h6, h5]
    have h4 : sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) ≥ 8 := by
      have h5 : (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64 : ℝ) ≥ 64 := by
        nlinarith [sq_nonneg (2 * x + 3 * y), sq_nonneg (x - 3 / 2), sq_nonneg (y + 1), sq_nonneg ((2 * x + 3 * y) + 2)]
      have h6 : sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) ≥ sqrt (64 : ℝ) := Real.sqrt_le_sqrt (by linarith)
      have h7 : sqrt (64 : ℝ) = (8 : ℝ) := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      nlinarith [h7, h6]
    have h5 : sqrt (4 * x ^ 2 - 12 * x + 25) + sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) ≥ 12 := by 
      linarith [h3, h4]
    have h6 : sqrt (4 * x ^ 2 - 12 * x + 25) + sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) = 12 := by
      linarith [h, h5]
    have h7 : sqrt (4 * x ^ 2 - 12 * x + 25) = 4 := by
      linarith [h6, h3, h4]
    have h8 : sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) = 8 := by
      linarith [h6, h7, h4]
    have h9 : 4 * x ^ 2 - 12 * x + 25 = 16 := by
      calc
        4 * x ^ 2 - 12 * x + 25 = (sqrt (4 * x ^ 2 - 12 * x + 25)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (4 : ℝ) ^ 2 := by
          rw [h7]
        _ = (16 : ℝ) := by 
          norm_num
    have h10 : x = 3 / 2 := by
      nlinarith 
    have h11 : 4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64 = 64 := by
      calc
        4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64 = (sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64)) ^ 2 := by 
          rw [Real.sq_sqrt]
          linarith
        _ = (8 : ℝ) ^ 2 := by 
          rw [h8]
        _ = (64 : ℝ) := by 
          norm_num
    have h12 : 4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 = 0 := by
      linarith [h11, h10]
    have h13 : 2 * x + 3 * y = 0 := by
      nlinarith [h12, h10]
    have h14 : y = -1 := by
      nlinarith [h13, h10]
    exact ⟨h10, h14⟩
  · -- Show that (x = 3/2 ∧ y = -1) satisfies the inequality
    rintro ⟨hx, hy⟩
    have h13 : 4 * x ^ 2 - 12 * x + 25 = 16 := by 
      rw [hx]
      norm_num
    have h14 : 4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64 = 64 := by 
      rw [hx, hy]
      norm_num
    have h15 : sqrt (4 * x ^ 2 - 12 * x + 25) = (4 : ℝ) := by
      rw [h13]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h16 : sqrt (4 * x ^ 2 + 12 * x * y + 9 * y ^ 2 + 64) = (8 : ℝ) := by
      rw [h14]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h15, h16]
    all_goals linarith