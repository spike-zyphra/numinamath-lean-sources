import Mathlib

theorem algebra_243580 {x y : ℝ} (h₁ : 3^x + 3^(y + 1) = 5 * Real.sqrt 3) (h₂ : 3^(x + 1) + 3^y = 3 * Real.sqrt 3) :
    3^x + 3^y = 2 * Real.sqrt 3 := by
  have eq1 : (3 : ℝ) ^ x + (3 : ℝ) ^ (y + 1) = (3 : ℝ) ^ x + 3 * (3 : ℝ) ^ y := by 
    rw [Real.rpow_add]
    ring_nf
    all_goals linarith
  have eq2 : (3 : ℝ) ^ (x + 1) + (3 : ℝ) ^ y = 3 * (3 : ℝ) ^ x + (3 : ℝ) ^ y := by 
    rw [Real.rpow_add]
    ring_nf
    all_goals linarith
  rw [eq1] at h₁
  rw [eq2] at h₂
  linarith [h₁, h₂]