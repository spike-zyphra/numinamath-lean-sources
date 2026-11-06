import Mathlib

theorem algebra_156381 {x y z : ℝ} (h : x^2 + y^2 = x * y * (z + 1 / z)) :
    x = y * z ∨ y = x * z := by
  by_cases h1 : z = 0
  · -- Case z = 0 
    have h2 : x^2 + y^2 = 0 := by
      rw [h1] at h 
      norm_num [h1] at h ⊢ 
      linarith 
    have hx1 : x^2 ≥ 0 := sq_nonneg x 
    have hy1 : y^2 ≥ 0 := sq_nonneg y 
    have h3 : x^2 = 0 := by 
      nlinarith 
    have hx0 : x = 0 := pow_eq_zero h3 
    have h4 : y^2 = 0 := by 
      nlinarith 
    have hy0 : y = 0 := pow_eq_zero h4 
    left 
    rw [hx0, hy0, h1]
    all_goals 
      norm_num 
  · -- Case z ≠ 0 
    have h2 : z ≠ 0 := by 
      intro h3 
      apply h1 
      all_goals 
        linarith 
    have eq1 : (x^2 + y^2) * z = x * y * (z^2 + 1) := by
      have h2' : x^2 + y^2 = x * y * (z + 1 / z) := h 
      field_simp [h2] at h2' ⊢ 
      nlinarith 
    have h3 : (x - y * z) * (y - x * z) = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (z - 1), sq_nonneg (z + 1), sq_nonneg (x * z - y), sq_nonneg (x - y * z), sq_nonneg (y - x * z)]
    cases' (mul_eq_zero.1 h3) with h4 h5 
    · -- Case x - y * z = 0 
      left 
      linarith 
    · -- Case y - x * z = 0 
      right 
      linarith