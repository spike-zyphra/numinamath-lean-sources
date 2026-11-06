import Mathlib


theorem number_theory_101572 (n : ℕ) :
    ∃ q : ℚ, Real.sqrt ((20 ^ n - 18 ^ n) / 19) = q ↔ n = 0 ∨ n = 2 := by
  by_cases h1 : n = 0
  · -- n = 0
    use (0 : ℚ)
    rw [h1]
    norm_num [Real.sqrt_eq_iff_sq_eq]
  · -- n ≠ 0
    by_cases h2 : n = 2
    · -- n = 2
      use (2 : ℚ)
      rw [h2]
      norm_num [Real.sqrt_eq_iff_sq_eq]
    · -- n ≠ 0 and n ≠ 2
      use (0 : ℚ)
      constructor
      · -- Assume sqrt ((20 ^ n - 18 ^ n) / 19) = (0 : ℚ), prove n = 0 ∨ n = 2
        intro h
        have h3 : n > 0 := by
          by_contra h4
          push_neg at h4
          have h4' : n = 0 := by linarith
          tauto
        have h4 : (20 ^ n - 18 ^ n : ℝ) / 19 > 0 := by
          have h5 : (20 ^ n : ℝ) > (18 ^ n : ℝ) := by
            have h6 : (20 : ℝ) > (18 : ℝ) := by norm_num
            have h7 : (20 : ℝ) ^ n > (18 : ℝ) ^ n := by
              apply pow_lt_pow_left
              all_goals nlinarith
            linarith
          have h8 : (20 ^ n - 18 ^ n : ℝ) > 0 := by nlinarith
          positivity
        have h8 : Real.sqrt ((20 ^ n - 18 ^ n) / 19) > 0 := by
          apply Real.sqrt_pos.mpr
          positivity
        have h9 : Real.sqrt ((20 ^ n - 18 ^ n) / 19) = (0 : ℚ) := by
          simpa using h
        nlinarith
      · -- Assume n = 0 ∨ n = 2, prove sqrt ((20 ^ n - 18 ^ n) / 19) = (0 : ℚ)
        intro h
        rcases h with (h3 | h3)
        · -- n = 0
          exfalso
          tauto
        · -- n = 2
          exfalso
          tauto