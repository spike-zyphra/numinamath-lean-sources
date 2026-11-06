import Mathlib

theorem inequalities_61877 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 4 - y ^ 4 = x - y) :
    (x - y) / (x ^ 6 - y ^ 6) ≤ 4 / 3 * (x + y) := by

  have h1 : x ^ 4 - y ^ 4 = (x - y) * (x + y) * (x^2 + y^2) := by 
    ring 
  have h2 : (x - y) * (x + y) * (x^2 + y^2) = x - y := by 
    linarith [h, h1]

  by_cases h3 : x - y = 0 
  · -- Case x - y = 0, so x = y 
    have h4 : x = y := by linarith 
    rw [h4] 
    norm_num 
    all_goals try positivity 
  · -- Case x - y ≠ 0 
    have h4 : (x + y) * (x^2 + y^2) = 1 := by 
      have h5 : (x - y) * (x + y) * (x^2 + y^2) = x - y := by 
        linarith [h2]
      have h6 : x - y ≠ 0 := by 
        intro h7 
        apply h3 
        linarith 
      have h7 : (x + y) * (x^2 + y^2) = 1 := by 
        apply (mul_left_inj' (show x - y ≠ 0 by exact h6)).mp 
        linarith 
      linarith

    by_cases h5 : x > y 
    · -- Case x > y, so x - y > 0 and x ^ 6 - y ^ 6 > 0 
      have h6 : x ^ 6 - y ^ 6 > 0 := by 
        have h7 : x ^ 2 > y ^ 2 := by 
          nlinarith [h5, sq_pos_of_pos hx, sq_pos_of_pos hy] 
        have h8 : x ^ 6 > y ^ 6 := by 
          have h9 : x ^ 2 > y ^ 2 := h7 
          have h10 : x ^ 6 = (x ^ 2) ^ 3 := by ring 
          have h11 : y ^ 6 = (y ^ 2) ^ 3 := by ring 
          rw [h10, h11] 
          have h12 : (x ^ 2) ^ 3 > (y ^ 2) ^ 3 := by 
            have h13 : x ^ 2 > y ^ 2 := h7 
            have h14 : x ^ 2 > y ^ 2 := h13 
            have h15 : (x ^ 2) ^ 3 > (y ^ 2) ^ 3 := by 
              apply pow_lt_pow_left 
              all_goals nlinarith 
            linarith 
          linarith 
        linarith 
      have h7 : (x - y) / (x ^ 6 - y ^ 6) ≤ 4 / 3 * (x + y) := by 
        apply (div_le_iff₀ h6).mpr 
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2), sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 3 + y ^ 3), h4, mul_pos hx hy, mul_pos hx (show (0 : ℝ) < y by linarith [hy])]
      linarith 
    -- Consider case x ≤ y 
    by_cases h6 : x < y 
    · -- Case x < y, so x - y < 0 and x ^ 6 - y ^ 6 < 0 
      have h7 : x ^ 6 - y ^ 6 < 0 := by 
        have h8 : x ^ 2 < y ^ 2 := by 
          nlinarith [h6, sq_pos_of_pos hx, sq_pos_of_pos hy] 
        have h9 : x ^ 6 < y ^ 6 := by 
          have h10 : x ^ 2 < y ^ 2 := h8 
          have h10' : x ^ 6 = (x ^ 2) ^ 3 := by ring 
          have h11' : y ^ 6 = (y ^ 2) ^ 3 := by ring 
          rw [h10', h11'] 
          have h12 : (x ^ 2) ^ 3 < (y ^ 2) ^ 3 := by 
            have h13 : x ^ 2 < y ^ 2 := h8 
            have h14 : x ^ 2 < y ^ 2 := h13 
            have h15 : (x ^ 2) ^ 3 < (y ^ 2) ^ 3 := by 
              apply pow_lt_pow_left 
              all_goals nlinarith 
            linarith 
          linarith 
        linarith 
      have h8 : (x - y) / (x ^ 6 - y ^ 6) ≤ 4 / 3 * (x + y) := by 
        apply (div_le_iff_of_neg' h7).mpr 
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2), sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 3 + y ^ 3), h4, mul_pos hx hy, mul_pos hx (show (0 : ℝ) < y by linarith [hy])]
      linarith 
    -- Case x = y, which is impossible as h3 : x - y ≠ 0 
    have h7 : x = y := by 
      nlinarith 
    have h8 : x - y = 0 := by linarith [h7] 
    contradiction