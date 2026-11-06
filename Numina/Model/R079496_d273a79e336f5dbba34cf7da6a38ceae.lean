import Mathlib

theorem algebra_207285 (f : ℝ → ℝ) (hf : f = fun x => x^2 - 41 * x + 330 - 3^x * (41 - 2 * x - 3^x)) :
    ∑ᶠ x ∈ {x | f x = 0}, x = 5 := by 
  have h1 : {x | f x = 0} = {2, 3} := by
    ext x
    simp [hf]
    constructor
    · -- Assume f(x) = 0, prove x ∈ {2, 3}
      intro h
      -- The equation is x^2 - 41 x + 330 = 3^x * (41 - 2 * x - 3^x)
      have h2 : x^2 - 41 * x + 330 - (3 : ℝ) ^ x * (41 - 2 * x - (3 : ℝ) ^ x) = 0 := by 
        linarith
      have eq1 : x^2 - 41 * x + 330 - (3 : ℝ) ^ x * (41 - 2 * x - (3 : ℝ) ^ x) =
        ((3 : ℝ) ^ x + x - 30) * ((3 : ℝ) ^ x + x - 11) := by
          ring_nf
      rw [eq1] at h2
      cases' (mul_eq_zero.mp h2) with h3 h4
      · -- Case h3: (3 : ℝ) ^ x + x - 30 = 0
        have h5 : (3 : ℝ) ^ x + x = 30 := by linarith 
        have h6 : x = 3 := by
          by_cases h7 : x < (3 : ℝ)
          · -- Assume x < 3
            have h8 : (3 : ℝ) ^ x < (3 : ℝ) ^ (3 : ℝ) := by 
              apply Real.rpow_lt_rpow_of_exponent_lt 
              all_goals linarith
            have h9 : (3 : ℝ) ^ (3 : ℝ) = 27 := by norm_num
            have h10 : (3 : ℝ) ^ x < 27 := by linarith [h9, h8]
            have h11 : x < (3 : ℝ) := h7
            nlinarith
          by_cases h8 : x > (3 : ℝ)
          · -- Assume x > 3
            have h9 : (3 : ℝ) ^ x > (3 : ℝ) ^ (3 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_lt 
              all_goals linarith
            have h10 : (3 : ℝ) ^ (3 : ℝ) = 27 := by norm_num
            have h11 : (3 : ℝ) ^ x > 27 := by linarith [h10, h9]
            have h12 : x > (3 : ℝ) := h8
            nlinarith
          linarith
        right
        linarith
      · -- Case h4: (3 : ℝ) ^ x + x - 11 = 0
        have h6 : (3 : ℝ) ^ x + x = 11 := by linarith 
        have h7 : x = 2 := by
          by_cases h8 : x < (2 : ℝ)
          · -- Assume x < 2
            have h9 : (3 : ℝ) ^ x < (3 : ℝ) ^ (2 : ℝ) := by 
              apply Real.rpow_lt_rpow_of_exponent_lt 
              all_goals linarith
            have h10 : (3 : ℝ) ^ (2 : ℝ) = 9 := by norm_num
            have h11 : (3 : ℝ) ^ x < 9 := by linarith [h10, h9]
            have h12 : x < (2 : ℝ) := h8
            nlinarith
          by_cases h9 : x > (2 : ℝ)
          · -- Assume x > 2
            have h10 : (3 : ℝ) ^ x > (3 : ℝ) ^ (2 : ℝ) := by
              apply Real.rpow_lt_rpow_of_exponent_lt 
              all_goals linarith
            have h11 : (3 : ℝ) ^ (2 : ℝ) = 9 := by norm_num
            have h12 : (3 : ℝ) ^ x > 9 := by linarith [h11, h10]
            have h13 : x > (2 : ℝ) := h9
            nlinarith
          linarith
        left
        linarith
    · -- Assume x ∈ {2, 3}, prove f(x) = 0
      rintro (rfl | rfl)
      · -- x = 2
        norm_num [Real.rpow_natCast, mul_add, sub_eq_zero]
      · -- x = 3
        norm_num [Real.rpow_natCast, mul_add, sub_eq_zero]
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num