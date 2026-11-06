import Mathlib

theorem algebra_269628 (f : ℝ → ℝ) (hf : f = fun x => x^2 - 31 * x + 220 - 2^x * (31 - 2 * x - 2^x)) :
    ∑ᶠ x ∈ {x | f x = 0}, x^2 = 25 := by
  have h1 : {x | f x = 0} = {3, 4} := by
    ext x
    simp [hf]
    constructor
    · -- Assume f x = 0, prove x ∈ {3, 4}
      intro h
      have h_eq : x^2 - 31 * x + 220 = (2 : ℝ) ^ x * (31 - 2 * x - (2 : ℝ) ^ x) := by linarith
      have h_eq2 : (x + (2 : ℝ) ^ x) ^ 2 - 31 * (x + (2 : ℝ) ^ x) + 220 = 0 := by
        have h2 : (2 : ℝ) ^ x * (31 - 2 * x - (2 : ℝ) ^ x) = 31 * (2 : ℝ) ^ x - 2 * x * (2 : ℝ) ^ x - ((2 : ℝ) ^ x) ^ 2 := by 
          ring
        rw [h2] at h_eq
        nlinarith [Real.rpow_pos_of_pos (show 0 < (2 : ℝ) by norm_num) x]
      have h_eq3 : ((x + (2 : ℝ) ^ x) - 20) * ((x + (2 : ℝ) ^ x) - 11) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h_eq3) with h_eq4 h_eq5
      · -- Case x + 2^x = 20
        have h_eq5 : x + (2 : ℝ) ^ x = 20 := by linarith
        have h2 : x = 4 := by
          by_cases h3 : x < (4 : ℝ)
          · -- Assume x < 4
            have h4 : (2 : ℝ) ^ x < (16 : ℝ) := by
              have h5 : (2 : ℝ) ^ x < (2 : ℝ) ^ (4 : ℝ) := by
                apply Real.rpow_lt_rpow_of_exponent_lt
                · norm_num
                · linarith
              norm_num at h5 ⊢
              all_goals linarith
            have h6 : x + (2 : ℝ) ^ x < (20 : ℝ) := by
              nlinarith
            linarith
          · -- Case x >= 4
            by_cases h4 : x > (4 : ℝ)
            · -- Assume x > 4
              have h3 : (2 : ℝ) ^ x > (16 : ℝ) := by
                have h5 : (2 : ℝ) ^ (4 : ℝ) < (2 : ℝ) ^ x := by
                  apply Real.rpow_lt_rpow_of_exponent_lt
                  · norm_num
                  · linarith
                norm_num at h5 ⊢
                all_goals linarith
              have h6 : x + (2 : ℝ) ^ x > (20 : ℝ) := by
                nlinarith
              linarith
            · -- Case x = 4
              have h5 : x = (4 : ℝ) := by linarith
              linarith
        simp [h2]
      · -- Case x + 2^x = 11
        have h_eq6 : x + (2 : ℝ) ^ x = 11 := by linarith
        have h2 : x = 3 := by
          by_cases h3 : x < (3 : ℝ)
          · -- Assume x < 3
            have h4 : (2 : ℝ) ^ x < (8 : ℝ) := by
              have h5 : (2 : ℝ) ^ x < (2 : ℝ) ^ (3 : ℝ) := by
                apply Real.rpow_lt_rpow_of_exponent_lt
                · norm_num
                · linarith
              norm_num at h5 ⊢
              all_goals linarith
            have h6 : x + (2 : ℝ) ^ x < (11 : ℝ) := by
              nlinarith
            linarith
          · -- Case x >= 3
            by_cases h4 : x > (3 : ℝ)
            · -- Assume x > 3
              have h3 : (2 : ℝ) ^ x > (8 : ℝ) := by
                have h5 : (2 : ℝ) ^ (3 : ℝ) < (2 : ℝ) ^ x := by
                  apply Real.rpow_lt_rpow_of_exponent_lt
                  · norm_num
                  · linarith
                norm_num at h5 ⊢
                all_goals linarith
              have h6 : x + (2 : ℝ) ^ x > (11 : ℝ) := by
                nlinarith
              linarith
            · -- Case x = 3
              have h5 : x = (3 : ℝ) := by linarith
              linarith
        simp [h2]
    · -- Assume x ∈ {3, 4}, prove f x = 0
      rintro (rfl | rfl)
      · -- x = 3
        norm_num
      · -- x = 4
        norm_num
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num