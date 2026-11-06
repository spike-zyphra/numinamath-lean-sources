import Mathlib

theorem algebra_127267 (x : ℝ) (hx : x > 0) (h : x ^ 2014 + 2014 ^ 2013 = x ^ 2013 + 2014 ^ 2014) :
    x = 2014 := by

  have h1 : x ^ 2014 + (2014 : ℝ) ^ 2013 = x ^ 2013 + (2014 : ℝ) ^ 2014 := by 
    exact_mod_cast h

  have h2 : x ^ 2014 - x ^ 2013 = (2014 : ℝ) ^ 2014 - (2014 : ℝ) ^ 2013 := by
    nlinarith [h1]

  have h3 : x ^ 2013 * (x - 1) = (2014 : ℝ) ^ 2013 * (2013) := by
    nlinarith [h2]

  have h4 : x ≥ (2014 : ℝ) := by 
    by_contra h6
    push_neg at h6
    have h5 : x < (2014 : ℝ) := by 
      linarith 
    have h6' : x < (2014 : ℝ) := h5
    by_cases h7 : x ≤ (1 : ℝ)
    · -- Case where x ≤ 1, so x - 1 ≤ 0
      have h8 : x - 1 ≤ (0 : ℝ) := by 
        linarith 
      have h9 : x ^ 2013 ≥ (0 : ℝ) := by
        apply pow_nonneg 
        linarith 
      have h10 : x ^ 2013 * (x - 1) ≤ (0 : ℝ) := by 
        nlinarith [h8, h9]
      have h11 : (2014 : ℝ) ^ 2013 * (2013 : ℝ) > (0 : ℝ) := by
        positivity 
      nlinarith [h3, h10, h11]
    · -- Case where x > 1, so x - 1 > 0
      have h8 : x > (1 : ℝ) := by 
        by_contra h9
        push_neg at h9
        have : x ≤ (1 : ℝ) := by linarith 
        linarith [h7, this]
      have h9 : x ^ 2013 < (2014 : ℝ) ^ 2013 := by 
        have h10 : x < (2014 : ℝ) := by linarith [h6']
        have h11 : x ^ 2013 < (2014 : ℝ) ^ 2013 := by 
          apply pow_lt_pow_left
          all_goals linarith 
        linarith
      have h10 : x - 1 > (0 : ℝ) := by 
        nlinarith 
      have h11 : x ^ 2013 * (x - 1) < (2014 : ℝ) ^ 2013 * (2013 : ℝ) := by
        have h12 : x - 1 > (0 : ℝ) := h10
        have h13 : x ^ 2013 < (2014 : ℝ) ^ 2013 := h9
        have h4' : x ^ 2013 * (x - 1) < (2014 : ℝ) ^ 2013 * (x - 1) := by
          apply mul_lt_mul_of_pos_right
          linarith 
          all_goals linarith 
        have h5' : (2014 : ℝ) ^ 2013 * (x - 1) < (2014 : ℝ) ^ 2013 * (2013 : ℝ) := by
          apply mul_lt_mul_of_pos_left
          nlinarith 
          all_goals positivity 
        linarith
      nlinarith [h3, h11]

  have h5 : x ≤ (2014 : ℝ) := by 
    by_contra h6
    push_neg at h6
    have h6' : x > (2014 : ℝ) := by 
      linarith 
    have h9 : x ^ 2013 * (x - 1) > (2014 : ℝ) ^ 2013 * (2013 : ℝ) := by 
      have h10 : x > (2014 : ℝ) := h6'
      have h11 : x ^ 2013 > (2014 : ℝ) ^ 2013 := by
        apply pow_lt_pow_left
        all_goals linarith 
      have h12 : x - 1 > (2013 : ℝ) := by 
        nlinarith 
      nlinarith [sq_nonneg (x ^ 1006), sq_nonneg ((2014 : ℝ) ^ 1006), sq_nonneg (x - (2014 : ℝ)), sq_nonneg (x ^ 1007 - (2014 : ℝ) ^ 1007)]
    nlinarith [h3, h9]

  linarith [h4, h5]