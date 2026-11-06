import Mathlib

theorem algebra_325850 : ∑ᶠ x ∈ {x : ℝ | abs (x^2 - 3 * x + 2) + abs (x^2 + 2 * x - 3) = 11}, x = (-19 + 5 * Real.sqrt 97) / 20 := by
  have h1 : {x : ℝ | abs (x^2 - 3 * x + 2) + abs (x^2 + 2 * x - 3) = 11} = {(-6 / 5 : ℝ), (1 + Real.sqrt 97) / 4} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume abs (x^2 - 3 * x + 2) + abs (x^2 + 2 * x - 3) = 11, prove x ∈ {(-6 / 5 : ℝ), (1 + Real.sqrt 97) / 4}
      intro h
      by_cases h2 : x < -3
      · -- Case x < -3
        rw [abs_of_pos (show x^2 - 3 * x + 2 > 0 by nlinarith), abs_of_pos (show x^2 + 2 * x - 3 > 0 by nlinarith)] at h
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (97 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
      · -- Case -3 ≤ x ≤ 1
        by_cases h3 : x ≤ 1
        · -- Case -3 ≤ x ≤ 1
          rw [abs_of_nonneg (show x^2 - 3 * x + 2 ≥ 0 by nlinarith), abs_of_nonpos (show x^2 + 2 * x - 3 ≤ 0 by nlinarith)] at h
          have hx1 : x = (-6 / 5 : ℝ) := by
            nlinarith
          left
          linarith
        · -- Case 1 < x ≤ 2
          by_cases h4 : x ≤ 2
          · -- Case 1 < x ≤ 2
            rw [abs_of_nonpos (show x^2 - 3 * x + 2 ≤ 0 by nlinarith), abs_of_nonneg (show x^2 + 2 * x - 3 ≥ 0 by nlinarith)] at h
            nlinarith
          · -- Case x > 2
            rw [abs_of_nonneg (show x^2 - 3 * x + 2 ≥ 0 by nlinarith), abs_of_nonneg (show x^2 + 2 * x - 3 ≥ 0 by nlinarith)] at h
            have hx2 : x = (1 + Real.sqrt 97) / 4 := by
              have h2 : 2 * x^2 - x - 12 = 0 := by
                nlinarith
              have h3 : 2 * x^2 - x - 12 = (x - (1 + Real.sqrt 97) / 4) * (x - (1 - Real.sqrt 97) / 4) := by
                ring_nf
                rw [Real.sq_sqrt (by norm_num)]
                linarith
              rw [h3] at h2
              cases (mul_eq_zero.mp h2) with
              | inl h4 =>
                linarith
              | inr h5 =>
                nlinarith [Real.sqrt_pos.mpr (show (97 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
            right
            linarith
    · -- Assume x ∈ {(-6 / 5 : ℝ), (1 + Real.sqrt 97) / 4}, prove abs (x^2 - 3 * x + 2) + abs (x^2 + 2 * x - 3) = 11
      rintro (rfl | rfl)
      · -- Check x = -6/5
        norm_num [abs_of_nonneg, abs_of_nonpos]
      · -- Check (1 + Real.sqrt 97) / 4
        have h2 : Real.sqrt 97 > 0 := by positivity
        have h3 : ((1 + Real.sqrt 97) / 4 : ℝ) > 2 := by
          nlinarith [Real.sqrt_pos.mpr (show (97 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
        have h4 : ((1 + Real.sqrt 97) / 4 : ℝ) ^ 2 - 3 * ((1 + Real.sqrt 97) / 4 : ℝ) + 2 ≥ 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (97 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
        have h5 : ((1 + Real.sqrt 97) / 4 : ℝ) ^ 2 + 2 * ((1 + Real.sqrt 97) / 4 : ℝ) - 3 ≥ 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (97 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
        rw [abs_of_nonneg h4, abs_of_nonneg h5]
        nlinarith [Real.sqrt_pos.mpr (show (97 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
  rw [h1]
  rw [finsum_mem_pair (by
    nlinarith [Real.sqrt_pos.mpr (show (97 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
  )
  ]
  field_simp
  nlinarith [Real.sqrt_pos.mpr (show (97 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]