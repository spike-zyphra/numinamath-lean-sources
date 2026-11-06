import Mathlib

theorem algebra_88200 (x y z : ℝ) (hx : |x| ≠ 1 / Real.sqrt 3) (hy : |y| ≠ 1 / Real.sqrt 3)
    (hz : |z| ≠ 1 / Real.sqrt 3) (h : x + y + z = x * y * z) :
    (3 * x - x ^ 3) / (1 - 3 * x ^ 2) + (3 * y - y ^ 3) / (1 - 3 * y ^ 2) +
    (3 * z - z ^ 3) / (1 - 3 * z ^ 2) =
    (3 * x - x ^ 3) / (1 - 3 * x ^ 2) * (3 * y - y ^ 3) / (1 - 3 * y ^ 2) *
    (3 * z - z ^ 3) / (1 - 3 * z ^ 2) := by

  have h1 : (1 - 3 * x ^ 2) ≠ 0 := by 
    by_contra h1
    have h2 : x ^ 2 = 1 / 3 := by
      linarith
    have h3 : |x| = 1 / Real.sqrt 3 := by
      have h4 : x ^ 2 = 1 / 3 := h2
      have h5 : |x| = Real.sqrt (x ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h5, h4]
      have h9 : Real.sqrt (1 / 3) = 1 / Real.sqrt 3 := by
        field_simp [Real.sqrt_eq_iff_sq_eq]
      rw [h9]
    have h4 : |x| = 1 / Real.sqrt 3 := h3
    contradiction
  
  have h2 : (1 - 3 * y ^ 2) ≠ 0 := by
    by_contra h2
    have h3 : y ^ 2 = 1 / 3 := by
      linarith
    have h4 : |y| = 1 / Real.sqrt 3 := by
      have h5 : y ^ 2 = 1 / 3 := h3
      have h6 : |y| = Real.sqrt (y ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h6, h5]
      have h9 : Real.sqrt (1 / 3) = 1 / Real.sqrt 3 := by
        field_simp [Real.sqrt_eq_iff_sq_eq]
      rw [h9]
    have h5 : |y| = 1 / Real.sqrt 3 := h4
    contradiction
  
  have h3 : (1 - 3 * z ^ 2) ≠ 0 := by 
    by_contra h3
    have h4 : z ^ 2 = 1 / 3 := by
      linarith
    have h5 : |z| = 1 / Real.sqrt 3 := by
      have h6 : z ^ 2 = 1 / 3 := h4
      have h7 : |z| = Real.sqrt (z ^ 2) := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h7, h6]
      have h9 : Real.sqrt (1 / 3) = 1 / Real.sqrt 3 := by
        field_simp [Real.sqrt_eq_iff_sq_eq]
      rw [h9]
    have h6 : |z| = 1 / Real.sqrt 3 := h5
    contradiction
  
  have h4 : (3 * x - x ^ 3) / (1 - 3 * x ^ 2) + (3 * y - y ^ 3) / (1 - 3 * y ^ 2) + (3 * z - z ^ 3) / (1 - 3 * z ^ 2) =
      ( (3 * x - x ^ 3) * (1 - 3 * y ^ 2) * (1 - 3 * z ^ 2) + (3 * y - y ^ 3) * (1 - 3 * x ^ 2) * (1 - 3 * z ^ 2) + (3 * z - z ^ 3) * (1 - 3 * x ^ 2) * (1 - 3 * y ^ 2) ) / ((1 - 3 * x ^ 2) * (1 - 3 * y ^ 2) * (1 - 3 * z ^ 2)) := by 
    field_simp [h1, h2, h3]
    <;> ring
  
  have h5 : (3 * x - x ^ 3) / (1 - 3 * x ^ 2) * (3 * y - y ^ 3) / (1 - 3 * y ^ 2) * (3 * z - z ^ 3) / (1 - 3 * z ^ 2) =
      ( (3 * x - x ^ 3) * (3 * y - y ^ 3) * (3 * z - z ^ 3) ) / ((1 - 3 * x ^ 2) * (1 - 3 * y ^ 2) * (1 - 3 * z ^ 2)) := by 
    field_simp [h1, h2, h3]
    <;> ring
  
  rw [h4, h5]
  field_simp [h1, h2, h3]
  nlinarith [sq_nonneg (x * y + y * z + z * x), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
    sq_nonneg (x * y * z - (x + y + z)), sq_nonneg (x * y + y * z + z * x - 3), sq_nonneg (x + y + z - x * y * z),
    sq_pos_of_pos (show (3:ℝ) > 0 by norm_num)
  ]