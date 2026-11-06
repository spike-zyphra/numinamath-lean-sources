import Mathlib

theorem algebra_122372 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : 1 / (x * y) = x / z + 1) (h2 : 1 / (y * z) = y / x + 1) (h3 : 1 / (z * x) = z / y + 1) :
    x = 1 / Real.sqrt 2 ∧ y = 1 / Real.sqrt 2 ∧ z = 1 / Real.sqrt 2 := by

  have eq1 : z = x ^ 2 * y + x * y * z := by
    have h1' : x * y > 0 := mul_pos hx hy
    have h1'' : x * y * z > 0 := mul_pos (mul_pos hx hy) hz
    field_simp [show x * y ≠ 0 by positivity, show z ≠ 0 by positivity] at h1 ⊢
    nlinarith [h1, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have eq2 : x = y ^ 2 * z + x * y * z := by
    have h1' : y * z > 0 := mul_pos hy hz
    have h1'' : x * y * z > 0 := mul_pos (mul_pos hx hy) hz
    field_simp [show y * z ≠ 0 by positivity, show x ≠ 0 by positivity] at h2 ⊢
    nlinarith [h2, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have eq3 : y = z ^ 2 * x + x * y * z := by
    have h1' : z * x > 0 := mul_pos hz hx
    have h1'' : x * y * z > 0 := mul_pos (mul_pos hx hy) hz
    field_simp [show z * x ≠ 0 by positivity, show y ≠ 0 by positivity] at h3 ⊢
    nlinarith [h3, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have h4 : x = y := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
      sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]

  have h5 : y = z := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
      sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        h4]

  have h8 : x = z := by linarith

  have h9 : x ^ 2 = 1 / 2 := by
    rw [show y = x by linarith, show z = x by linarith] at eq1
    nlinarith [sq_pos_of_pos hx]

  have h11 : x = 1 / Real.sqrt 2 := by
    have h14 : x ^ 2 = 1 / 2 := h9
    have h16 : x > 0 := hx
    have h17 : x = Real.sqrt (1 / 2) := by
      have h18 : x ^ 2 = 1 / 2 := h14
      have h19 : x > 0 := h16
      have h47 : (Real.sqrt (1 / 2)) ^ 2 = 1 / 2 := by
        rw [Real.sq_sqrt]
        norm_num
      have h21 : x ^ 2 = (Real.sqrt (1 / 2)) ^ 2 := by linarith [h18, h47]
      have h22 : x = Real.sqrt (1 / 2) := by
        have h23 : x ≥ 0 := by linarith
        nlinarith [Real.sqrt_nonneg (1 / 2 : ℝ), sq_nonneg (x - Real.sqrt (1 / 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)]
      exact h22
    have h23 : Real.sqrt (1 / 2) = (1 / Real.sqrt 2 : ℝ) := by
      have h24 : Real.sqrt (1 / 2) = (Real.sqrt 1) / (Real.sqrt 2 : ℝ) := by
        rw [← Real.sqrt_div (by norm_num)]
      have h25 : (Real.sqrt 1 : ℝ) = (1 : ℝ) := Real.sqrt_one
      rw [h24, h25]
      all_goals
        norm_num
    rw [h23] at h17
    linarith

  have h12 : y = 1 / Real.sqrt 2 := by
    have h20 : y = x := by linarith [h4]
    rw [h11] at h20
    linarith

  have h13 : z = 1 / Real.sqrt 2 := by
    have h21 : z = y := by linarith [h5]
    rw [h12] at h21
    linarith

  exact ⟨h11, h12, h13⟩