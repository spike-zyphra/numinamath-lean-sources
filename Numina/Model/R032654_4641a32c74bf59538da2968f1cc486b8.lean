import Mathlib

theorem inequalities_6774 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x / (x + 1) + y / (y + 1) + z / (z + 1) = 3 / 2) :
    (x * y ^ 2 + x * z ^ 2) / (x * y * z + y * z) +
    (y * z ^ 2 + y * x ^ 2) / (y * z * x + z * x) +
    (z * x ^ 2 + z * y ^ 2) / (z * x * y + x * y) ≥ 3 := by

  have h1 : (x * y ^ 2 + x * z ^ 2) / (x * y * z + y * z) ≥ 2 * x / (x + 1) := by
    have h2 : x * y ^ 2 + x * z ^ 2 ≥ 2 * x * y * z := by
      have h2 : (y - z) ^ 2 ≥ 0 := by
        exact sq_nonneg (y - z)
      have h3 : y ^ 2 + z ^ 2 ≥ 2 * y * z := by
        linarith [h2]
      have h4 : x * (y ^ 2 + z ^ 2) ≥ x * (2 * y * z) := by
        apply mul_le_mul_of_nonneg_left
        linarith [h3]
        all_goals linarith
      nlinarith
    have h5 : x * y * z + y * z > 0 := by
      positivity
    have h6 : x + 1 > 0 := by
      linarith
    have h7 : (x * y ^ 2 + x * z ^ 2) / (x * y * z + y * z) ≥ 2 * x / (x + 1) := by
      have h9 : x * y * z + y * z = y * z * (x + 1) := by
        ring 
      rw [h9]
      apply (div_le_div_iff (by positivity) (by positivity)).mpr 
      nlinarith [h2, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    linarith [h7]

  have h2 : (y * z ^ 2 + y * x ^ 2) / (y * z * x + z * x) ≥ 2 * y / (y + 1) := by
    have h8 : y * z ^ 2 + y * x ^ 2 ≥ 2 * y * z * x := by
      have h2 : (z - x) ^ 2 ≥ 0 := by
        exact sq_nonneg (z - x)
      have h3 : z ^ 2 + x ^ 2 ≥ 2 * z * x := by
        linarith [h2]
      have h4 : y * (z ^ 2 + x ^ 2) ≥ y * (2 * z * x) := by
        apply mul_le_mul_of_nonneg_left
        linarith [h3]
        all_goals linarith
      nlinarith 
    have h9 : y * z * x + z * x > 0 := by
      positivity 
    have h10 : y + 1 > 0 := by 
      linarith 
    have h11 : (y * z ^ 2 + y * x ^ 2) / (y * z * x + z * x) ≥ 2 * y / (y + 1) := by
      have h9 : y * z * x + z * x = z * x * (y + 1) := by
        ring 
      rw [h9]
      apply (div_le_div_iff (by positivity) (by positivity)).mpr 
      nlinarith [h8, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    linarith [h11]

  have h3 : (z * x ^ 2 + z * y ^ 2) / (z * x * y + x * y) ≥ 2 * z / (z + 1) := by
    have h14 : z * x ^ 2 + z * y ^ 2 ≥ 2 * z * x * y := by
      have h2 : (x - y) ^ 2 ≥ 0 := by 
        exact sq_nonneg (x - y)
      have h3 : x ^ 2 + y ^ 2 ≥ 2 * x * y := by
        linarith [h2]
      have h4 : z * (x ^ 2 + y ^ 2) ≥ z * (2 * x * y) := by 
        apply mul_le_mul_of_nonneg_left 
        linarith [h3]
        all_goals linarith 
      nlinarith
    have h15 : z * x * y + x * y > 0 := by
      positivity 
    have h16 : z + 1 > 0 := by 
      linarith 
    have h17 : (z * x ^ 2 + z * y ^ 2) / (z * x * y + x * y) ≥ 2 * z / (z + 1) := by
      have h9 : z * x * y + x * y = x * y * (z + 1) := by 
        ring
      rw [h9]
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h14, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    linarith [h17]

  have h4 : (x * y ^ 2 + x * z ^ 2) / (x * y * z + y * z) +
      (y * z ^ 2 + y * x ^ 2) / (y * z * x + z * x) + 
      (z * x ^ 2 + z * y ^ 2) / (z * x * y + x * y) ≥ 
      2 * x / (x + 1) + 2 * y / (y + 1) + 2 * z / (z + 1) := by 
    linarith [h1, h2, h3]

  have h5 : 2 * x / (x + 1) + 2 * y / (y + 1) + 2 * z / (z + 1) = 
      2 * (x / (x + 1) + y / (y + 1) + z / (z + 1)) := by 
    ring 

  have h6 : 2 * (x / (x + 1) + y / (y + 1) + z / (z + 1)) = 3 := by 
    linarith [h]

  linarith [h4, h5, h6]