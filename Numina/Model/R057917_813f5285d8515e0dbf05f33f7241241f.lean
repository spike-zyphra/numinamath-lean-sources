import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_106694 :
  ¬∃ x : ℝ, x^2 - 2 * x + 3 ≤ sqrt (4 - x^2) := by 
  intro h
  rcases h with ⟨x, hx⟩
  have h1 : x^2 - 2 * x + 3 ≥ 2 := by
    nlinarith [sq_nonneg (x - 1)]
  have h2 : sqrt (4 - x^2) ≥ 0 := Real.sqrt_nonneg (4 - x^2)
  have h3 : x^2 - 2 * x + 3 ≤ sqrt (4 - x^2) := hx
  have h4 : 2 ≤ sqrt (4 - x^2) := by linarith [h1, h3]
  have h5 : sqrt (4 - x^2) ≤ 2 := by
    have h6 : 4 - x^2 ≤ (4 : ℝ) := by nlinarith [sq_nonneg x]
    have h7 : sqrt (4 - x^2) ≤ sqrt (4 : ℝ) := Real.sqrt_le_sqrt (h6)
    have h8 : sqrt (4 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    linarith [h7, h8]
  have h9 : sqrt (4 - x^2) = 2 := by linarith [h4, h5]
  have h10 : (4 - x^2) = (4 : ℝ) := by 
    calc 
      (4 - x^2) = (sqrt (4 - x^2)) ^ 2 := by rw [Real.sq_sqrt]; all_goals nlinarith [Real.sqrt_nonneg (4 - x^2)]
      _ = (2 : ℝ) ^ 2 := by rw [h9]
      _ = (4 : ℝ) := by norm_num
  have h11 : x^2 = (0 : ℝ) := by linarith 
  have h12 : x = (0 : ℝ) := by 
    nlinarith [sq_nonneg x]
  have h13 : x^2 - 2 * x + 3 = (2 : ℝ) := by linarith [h1, h3, h9]
  rw [h12] at h13
  norm_num at h13 
  all_goals linarith