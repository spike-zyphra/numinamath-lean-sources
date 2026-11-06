import Mathlib

theorem algebra_123148 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : x / (x + 2 * y + 3 * z) = 1 / 6) (h2 : y / (x + 2 * y + 3 * z) = 2 / 6)
    (h3 : z / (x + 2 * y + 3 * z) = 3 / 6) :
    x / (x + 8 * y + 11 * z) = 5 / 21 ∧ y / (x + 8 * y + 11 * z) = 8 / 21 ∧
    z / (x + 8 * y + 11 * z) = 11 / 21 := by

  have h4 : x + 2 * y + 3 * z ≠ 0 := by
    by_contra h
    have ht1 : x / (x + 2 * y + 3 * z) = 0 := by 
      rw [h]
      norm_num
    have ht2 : y / (x + 2 * y + 3 * z) = 0 := by 
      rw [h]
      norm_num
    have ht3 : z / (x + 2 * y + 3 * z) = 0 := by 
      rw [h]
      norm_num
    linarith [h1, ht1, h2, ht2, h3, ht3]

  field_simp [h4] at h1 h2 h3 
  have h8 : x + 2 * y + 3 * z = 0 := by 
    nlinarith 
  have h9 : x + 2 * y + 3 * z > 0 := by 
    nlinarith 
  linarith [h8, h9]