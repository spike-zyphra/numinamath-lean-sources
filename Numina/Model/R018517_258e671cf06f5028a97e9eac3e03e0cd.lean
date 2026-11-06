import Mathlib

theorem algebra_37153 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : 1 / (x * y) = x / z + 1) (h2 : 1 / (y * z) = y / x + 1) (h3 : 1 / (z * x) = z / y + 1) :
    x = 1 / Real.sqrt 2 ∧ y = 1 / Real.sqrt 2 ∧ z = 1 / Real.sqrt 2 := by

  have eq1 : z = x^2 * y + x * y * z := by
    have h1' : x * y ≠ 0 := mul_ne_zero (ne_of_gt hx) (ne_of_gt hy)
    have hz' : z ≠ 0 := ne_of_gt hz
    field_simp [h1', hz'] at h1
    nlinarith [h1, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have eq2 : x = y^2 * z + x * y * z := by
    have h2' : y * z ≠ 0 := mul_ne_zero (ne_of_gt hy) (ne_of_gt hz)
    have hx' : x ≠ 0 := ne_of_gt hx
    field_simp [h2', hx'] at h2
    nlinarith [h2, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have eq3 : y = x * z^2 + x * y * z := by
    have h3' : z * x ≠ 0 := mul_ne_zero (ne_of_gt hz) (ne_of_gt hx)
    have hy' : y ≠ 0 := ne_of_gt hy
    field_simp [h3', hy'] at h3
    nlinarith [h3, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have h4 : x = y := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
      sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      sq_nonneg (x * y - 1 / 2), sq_nonneg (y * z - 1 / 2), sq_nonneg (z * x - 1 / 2)]
  
  have h5 : y = z := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
      sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, 
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      sq_nonneg (x * y - 1 / 2), sq_nonneg (y * z - 1 / 2), sq_nonneg (z * x - 1 / 2)]
  
  have h6 : x = z := by
    nlinarith [h4, h5]

  have h7 : x^2 = 1 / 2 := by
    have h8 : x = y := h4
    have h9 : x = z := h6
    rw [show y = x by linarith [h8]] at eq1
    rw [show z = x by linarith [h9]] at eq1
    nlinarith [sq_nonneg (x - 1 / Real.sqrt 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  have h8 : x = 1 / Real.sqrt 2 := by
    have h9 : x^2 = 1 / 2 := h7
    have h10 : x > 0 := hx
    have h11 : x = Real.sqrt (1 / 2) := by
      have h13 : x > 0 := hx
      have h14 : x ^ 2 = 1 / (2 : ℝ) := h9
      have : x = Real.sqrt (1 / 2) := by
        rw [← h14]
        field_simp
      assumption

    have h12 : Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
      field_simp [Real.sqrt_eq_iff_sq_eq]
    
    rw [h12] at h11
    linarith

  constructor
  · exact h8
  constructor
  · -- Show y = 1 / Real.sqrt 2
    have hy' : y = x := by linarith [h4]
    rw [hy', h8]
  · -- Show z = 1 / Real.sqrt 2
    have hz' : z = x := by linarith [h6]
    rw [hz', h8]