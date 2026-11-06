import Mathlib

theorem algebra_62457 (φ : ℝ) (h : 7 / 13 + Real.sin φ = Real.cos φ) : Real.sin (2 * φ) = 120 / 169 := by 
  have h1 : Real.cos φ - Real.sin φ = 7 / 13 := by
    linarith
  have h2 : (Real.cos φ - Real.sin φ) ^ 2 = (7 / 13) ^ 2 := by
    rw [h1]
  have h3 : (Real.cos φ - Real.sin φ) ^ 2 = Real.cos φ ^ 2 - 2 * (Real.sin φ * Real.cos φ) + Real.sin φ ^ 2 := by
    ring
  have h4 : Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 := Real.cos_sq_add_sin_sq φ
  have eq1 : Real.cos φ ^ 2 - 2 * (Real.sin φ * Real.cos φ) + Real.sin φ ^ 2 = (7 / 13) ^ 2 := by
    linarith [h2, h3]
  have h5 : Real.sin (2 * φ) = 2 * Real.sin φ * Real.cos φ := by 
    rw [Real.sin_two_mul]
  have eq3 : 1 - (2 * Real.sin φ * Real.cos φ) = (7 / 13) ^ 2 := by
    nlinarith
  have eq4 : 2 * Real.sin φ * Real.cos φ = 1 - (7 / 13) ^ 2 := by 
    linarith
  have eq5 : Real.sin (2 * φ) = 1 - (7 / 13) ^ 2 := by
    calc 
      Real.sin (2 * φ) = 2 * Real.sin φ * Real.cos φ := by 
        rw [Real.sin_two_mul]
      _ = 1 - (7 / 13) ^ 2 := by 
        linarith [eq4]
  rw [eq5]
  norm_num