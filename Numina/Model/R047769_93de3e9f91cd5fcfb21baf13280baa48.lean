import Mathlib
open Real

theorem inequalities_3556 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x * y + y * z + z * x = 1) :
    1 / 6 + 1 / 2 * (x ^ 2 + y * z) / (x ^ 2 + 1 + y ^ 2 + z ^ 2) ≥
    Real.sqrt (x ^ 2 + y * z) / Real.sqrt (3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2) := by 
  have h12 : 1 / 6 + 1 / 2 * (x ^ 2 + y * z) / (x ^ 2 + 1 + y ^ 2 + z ^ 2) ≥ Real.sqrt (x ^ 2 + y * z) / Real.sqrt (3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2) := by
    have h15 : Real.sqrt (x ^ 2 + y * z) / Real.sqrt (3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2) ≥ 0 := by positivity
    have h34 : 1 / 6 + 1 / 2 * (x ^ 2 + y * z) / (x ^ 2 + 1 + y ^ 2 + z ^ 2) ≥ 0 := by
      have h17 : 0 ≤ (x ^ 2 + y * z) := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, h]
      have h24 : (x ^ 2 + 1 + y ^ 2 + z ^ 2) > 0 := by
        nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, h]
      positivity
    -- Now we need to show that the original left side is greater than or equal to the right side.
    -- Since squaring is a monotone operation for non-negative numbers, we can take square roots.
    have h16 : (Real.sqrt (x ^ 2 + y * z) / Real.sqrt (3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2)) ^ 2 ≤ (1 / 6 + 1 / 2 * (x ^ 2 + y * z) / (x ^ 2 + 1 + y ^ 2 + z ^ 2)) ^ 2 := by
      have h17 : (Real.sqrt (x ^ 2 + y * z) / Real.sqrt (3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2)) ^ 2
        = (x ^ 2 + y * z) / (3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2) := by
        have h18 : (Real.sqrt (3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2)) ^ 2 = 3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        have h19 : (Real.sqrt (x ^ 2 + y * z)) ^ 2 = x ^ 2 + y * z := by
          rw [Real.sq_sqrt]
          positivity
        field_simp [h18, h19]
      have h20 : (1 / 6 + 1 / 2 * (x ^ 2 + y * z) / (x ^ 2 + 1 + y ^ 2 + z ^ 2)) ^ 2 = (1 / 36 + (x ^ 2 + y * z) / (6 * (x ^ 2 + 1 + y ^ 2 + z ^ 2)) + (x ^ 2 + y * z) ^ 2 / (4 * (x ^ 2 + 1 + y ^ 2 + z ^ 2) ^ 2)) := by
        field_simp
        ring
      rw [h17, h20]
      have h21 : (x ^ 2 + 1 + y ^ 2 + z ^ 2) > 0 := by 
        nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, h]
      have h24 : (x ^ 2 + 1 + y ^ 2 + z ^ 2) > 0 := h21
      -- Now we need to show that the left side squared is greater than the right side squared.
      have h26 : (1 / 36 + (x ^ 2 + y * z) / (6 * (x ^ 2 + 1 + y ^ 2 + z ^ 2)) + (x ^ 2 + y * z) ^ 2 / (4 * (x ^ 2 + 1 + y ^ 2 + z ^ 2) ^ 2)) ≥ (x ^ 2 + y * z) / (3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2) := by
        have h21' : (x ^ 2 + 1 + y ^ 2 + z ^ 2) > 0 := h21
        have h22 : 0 < 3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z, h]
        have h27 : (1 / 36 + (x ^ 2 + y * z) / (6 * (x ^ 2 + 1 + y ^ 2 + z ^ 2)) + (x ^ 2 + y * z) ^ 2 / (4 * (x ^ 2 + 1 + y ^ 2 + z ^ 2) ^ 2)) - (x ^ 2 + y * z) / (3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2) ≥ 0 := by
          have h28 : (1 / 36 + (x ^ 2 + y * z) / (6 * (x ^ 2 + 1 + y ^ 2 + z ^ 2)) + (x ^ 2 + y * z) ^ 2 / (4 * (x ^ 2 + 1 + y ^ 2 + z ^ 2) ^ 2)) - (x ^ 2 + y * z) / (3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2) =
            ((x^2 + 1 + y^2 + z^2)^2 - 6 * (x ^ 2 + y * z) * (x^2 + 1 + y^2 + z^2) + 9 * (x^2 + y * z)^2) / (36 * (x^2 + 1 + y^2 + z^2)^2) := by
            field_simp
            nlinarith [h, sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
          rw [h28]
          have h18 : (x^2 + 1 + y^2 + z^2)^2 - 6 * (x ^ 2 + y * z) * (x^2 + 1 + y^2 + z^2) + 9 * (x^2 + y * z)^2 ≥ 0 := by
            have h22 : (x^2 + 1 + y^2 + z^2)^2 - 6 * (x ^ 2 + y * z) * (x^2 + 1 + y^2 + z^2) + 9 * (x^2 + y * z)^2 = ((x^2 + 1 + y^2 + z^2) - 3 * (x^2 + y * z))^2 := by 
              nlinarith
            rw [h22]
            apply sq_nonneg
          apply div_nonneg
          linarith
          positivity
        linarith
      linarith
    have h23 : Real.sqrt (x ^ 2 + y * z) / Real.sqrt (3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2) ≥ 0 := by positivity
    have h34' : (1 / 6 + 1 / 2 * (x ^ 2 + y * z) / (x ^ 2 + 1 + y ^ 2 + z ^ 2)) ≥ 0 := h34
    nlinarith [Real.sqrt_nonneg (x ^ 2 + y * z), Real.sqrt_nonneg (3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2), Real.sq_sqrt (show 0 ≤ (x ^ 2 + y * z) by positivity), Real.sq_sqrt (show 0 ≤ (3 * x ^ 2 + 3 + 3 * y ^ 2 + 3 * z ^ 2) by positivity), h16, h34, h23]
  exact h12