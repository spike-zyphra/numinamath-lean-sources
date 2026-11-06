import Mathlib

theorem algebra_167114 (x : ℝ) :
    2020^(x^2 - 2 * x) + (x^2 - 2 * x) / 2020^x = 1 ↔ x = 0 ∨ x = 2 := by 
  constructor 
  · -- Assume the equation holds, prove x = 0 or x = 2
    intro h 
    by_cases h1 : x^2 - 2 * x < 0 
    · -- Case where x^2 - 2 * x < 0
      have h2 : (2020 : ℝ) ^ (x ^ 2 - 2 * x) < (1 : ℝ) := by 
        have h3 : (2020 : ℝ) ^ (x ^ 2 - 2 * x) < (2020 : ℝ) ^ (0 : ℝ) := by 
          apply Real.rpow_lt_rpow_of_exponent_lt 
          · norm_num 
          · linarith 
        norm_num at h3 ⊢ 
        linarith 
      have h4 : (x^2 - 2 * x) / (2020 : ℝ) ^ x < (0 : ℝ) := by 
        have h5 : (x^2 - 2 * x) < (0 : ℝ) := by nlinarith 
        have h6 : (2020 : ℝ) ^ x > (0 : ℝ) := by positivity 
        apply div_neg_of_neg_of_pos 
        · linarith 
        · linarith 
      have h8 : (2020 : ℝ) ^ (x ^ 2 - 2 * x) + (x ^ 2 - 2 * x) / (2020 : ℝ) ^ x < (1 : ℝ) := by 
        nlinarith 
      linarith 
    · -- Case where x^2 - 2 * x ≥ 0 
      have h1' : x^2 - 2 * x ≥ 0 := by linarith 
      by_cases h2 : x^2 - 2 * x > (0 : ℝ) 
      · -- Case where x^2 - 2 * x > 0 
        by_cases ha1 : x > (2 : ℝ) 
        · -- Case where x > 2. We will derive a contradiction. 
          have h3 : (2020 : ℝ) ^ (x ^ 2 - 2 * x) > (1 : ℝ) := by 
            have h4 : (2020 : ℝ) ^ (x ^ 2 - 2 * x) > (2020 : ℝ) ^ (0 : ℝ) := by 
              apply Real.rpow_lt_rpow_of_exponent_lt 
              · norm_num 
              · nlinarith 
            norm_num at h4 ⊢ 
            linarith 
          have h4 : (x^2 - 2 * x) / (2020 : ℝ) ^ x > (0 : ℝ) := by 
            have h5 : (x^2 - 2 * x) > (0 : ℝ) := by nlinarith 
            have h6 : (2020 : ℝ) ^ x > (0 : ℝ) := by positivity 
            positivity 
          have h5 : (2020 : ℝ) ^ (x ^ 2 - 2 * x) + (x ^ 2 - 2 * x) / (2020 : ℝ) ^ x > (1 : ℝ) := by 
            nlinarith 
          linarith 
        · -- Case where x ≤ 2. We will show this is invalid for x^2 - 2x > 0. 
          have h3 : x ≤ (2 : ℝ) := by linarith 
          have h5 : x < (0 : ℝ) := by 
            nlinarith [sq_nonneg (x - 2), sq_nonneg (x), sq_nonneg (x + 2)]
          have h3 : (2020 : ℝ) ^ (x ^ 2 - 2 * x) > (1 : ℝ) := by 
            have h4 : (2020 : ℝ) ^ (x ^ 2 - 2 * x) > (2020 : ℝ) ^ (0 : ℝ) := by 
              apply Real.rpow_lt_rpow_of_exponent_lt 
              · norm_num 
              · nlinarith 
            norm_num at h4 ⊢ 
            linarith 
          have h4 : (x^2 - 2 * x) / (2020 : ℝ) ^ x > (0 : ℝ) := by 
            have h5 : (x^2 - 2 * x) > (0 : ℝ) := by nlinarith 
            have h6 : (2020 : ℝ) ^ x > (0 : ℝ) := by positivity 
            positivity 
          have h5 : (2020 : ℝ) ^ (x ^ 2 - 2 * x) + (x ^ 2 - 2 * x) / (2020 : ℝ) ^ x > (1 : ℝ) := by 
            nlinarith 
          linarith 
      · -- Case where x^2 - 2 * x = 0. 
        have h3 : (x^2 - 2 * x) = (0 : ℝ) := by nlinarith 
        have h4 : x^2 - 2 * x = 0 := by linarith 
        have h5 : x * (x - 2) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.mp h5) with h51 h52 
        · -- Case where $x=0$, which is the first side of the `or`. 
          left 
          linarith 
        · -- Case where x - 2 = 0, hence x = 2. 
          right 
          linarith 
  · -- Assume x = 0 or x = 2, prove the equation 
    rintro (h | h) 
    · -- Case where x = 0 
      rw [h] 
      have h1 : (0 : ℝ) ^ 2 - 2 * (0 : ℝ) = (0 : ℝ) := by ring 
      rw [h1] 
      norm_num 
    · -- Case where x = 2 
      rw [h] 
      have h1 : (2 : ℝ) ^ 2 - 2 * (2 : ℝ) = (0 : ℝ) := by ring 
      rw [h1] 
      norm_num