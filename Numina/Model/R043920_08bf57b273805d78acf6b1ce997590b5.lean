import Mathlib

open Real

theorem inequalities_298089 (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : (x - 1) ^ ((1 : ℝ) / y) + (y - 1) ^ ((1 : ℝ) / y) ≤ 2) :
    x + y ≥ x * y := by
  have h1 : x - 1 ≥ 0 := by linarith
  have h2 : y - 1 ≥ 0 := by linarith
  have h3 : (x - 1) ^ ((1 : ℝ) / y) ≥ 0 := by positivity
  have h4 : (y - 1) ^ ((1 : ℝ) / y) ≥ 0 := by positivity
  have h5 : ((x - 1) ^ ((1 : ℝ) / y)) ^ (y : ℝ) = x - 1 := by
    rw [← Real.rpow_mul]
    field_simp
    all_goals linarith
  have h6 : ((y - 1) ^ ((1 : ℝ) / y)) ^ (y : ℝ) = y - 1 := by
    rw [← Real.rpow_mul]
    field_simp
    all_goals linarith
  have h7 : (x - 1) * (y - 1) = ((x - 1) ^ ((1 : ℝ) / y) * (y - 1) ^ ((1 : ℝ) / y)) ^ (y : ℝ) := by
    calc
      (x - 1) * (y - 1) = ((x - 1) ^ ((1 : ℝ) / y)) ^ (y : ℝ) * ((y - 1) ^ ((1 : ℝ) / y)) ^ (y : ℝ) := by
        rw [h5, h6]
      _ = ((x - 1) ^ ((1 : ℝ) / y) * (y - 1) ^ ((1 : ℝ) / y)) ^ (y : ℝ) := by
        rw [Real.mul_rpow]
        all_goals linarith
  have h8 : (x - 1) ^ ((1 : ℝ) / y) * (y - 1) ^ ((1 : ℝ) / y) ≤ 1 := by
    nlinarith [sq_nonneg ((x - 1) ^ ((1 : ℝ) / y) - 1), sq_nonneg ((y - 1) ^ ((1 : ℝ) / y) - 1),
      h, mul_nonneg h3 h4]
  have h9 : ((x - 1) ^ ((1 : ℝ) / y) * (y - 1) ^ ((1 : ℝ) / y)) ^ (y : ℝ) ≤ (1 : ℝ) := by
    have h10 : (x - 1) ^ ((1 : ℝ) / y) * (y - 1) ^ ((1 : ℝ) / y) ≤ (1 : ℝ) := by
      linarith
    have h11 : ((x - 1) ^ ((1 : ℝ) / y) * (y - 1) ^ ((1 : ℝ) / y)) ^ (y : ℝ) ≤ (1 : ℝ) ^ (y : ℝ) := by
      apply Real.rpow_le_rpow
      all_goals nlinarith
    have h12 : (1 : ℝ) ^ (y : ℝ) = 1 := by
      simp
    linarith [h11, h12]
  have h10 : (x - 1) * (y - 1) ≤ (1 : ℝ) := by
    linarith [h7, h9]
  nlinarith [h10, mul_self_nonneg (x - 1), mul_self_nonneg (y - 1)]