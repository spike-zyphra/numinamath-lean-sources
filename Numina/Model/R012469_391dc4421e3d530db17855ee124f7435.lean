import Mathlib

theorem algebra_205840 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h₁ : 1/x - 1/y = 4) (h₂ : x * y = 1 / 4) :
    1 / x ^ 4 + 1 / y ^ 4 = 544 := by
  have eq1 : y - x = 1 := by 
    have eq2 : 1 / x - 1 / y = (y - x) / (x * y) := by 
      field_simp [hx, hy]
      <;> ring 
    rw [eq2] at h₁
    rw [show x * y = 1 / 4 by linarith] at h₁ 
    field_simp at h₁ 
    linarith 
  have eq2 : y = x + 1 := by linarith 
  have eq3 : x ^ 2 + x - 1 / 4 = 0 := by
    have h3 : x * y = 1 / 4 := h₂
    rw [eq2] at h3
    nlinarith 
  have eq4 : x ^ 2 + y ^ 2 = 3 / 2 := by
    have h3 : y = x + 1 := eq2 
    rw [h3]
    nlinarith [sq_nonneg (2 * x + 1)]
  have eq6 : x ^ 4 + y ^ 4 = 17 / 8 := by
    have h10 : x ^ 2 + y ^ 2 = 3 / 2 := eq4
    have h11 : x * y = 1 / 4 := h₂
    calc 
      x ^ 4 + y ^ 4 = (x ^ 2 + y ^ 2) ^ 2 - 2 * (x * y) ^ 2 := by 
        ring 
      _ = (3 / 2) ^ 2 - 2 * (1 / 4) ^ 2 := by 
        rw [h10, h11]
      _ = 17 / 8 := by 
        norm_num 
  have eq8 : 1 / x ^ 4 + 1 / y ^ 4 = (x ^ 4 + y ^ 4) / ( (x * y) ^ 4 ) := by 
    field_simp [hx, hy]
    <;> ring 
  rw [eq8]
  have eq6' : x ^ 4 + y ^ 4 = 17 / 8 := eq6 
  rw [eq6']
  have eq9 : (x * y) ^ 4 = (1 / 4) ^ 4 := by 
    rw [h₂]
  rw [eq9]
  all_goals norm_num