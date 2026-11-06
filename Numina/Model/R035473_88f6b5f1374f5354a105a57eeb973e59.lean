import Mathlib

theorem algebra_11662 : ∑ᶠ x ∈ {x : ℝ | abs (x ^ 2 - 3 * x + 2) + abs (x ^ 2 + 2 * x - 3) = 11}, x = (-19 + 5 * Real.sqrt 97) / 20 := by

  have h1 : {x : ℝ | abs (x ^ 2 - 3 * x + 2) + abs (x ^ 2 + 2 * x - 3) = 11} = {-6/5, (1 + Real.sqrt 97)/4} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume abs (x ^ 2 - 3 * x + 2) + abs (x ^ 2 + 2 * x - 3) = 11, prove x ∈ {-6/5, (1 + Real.sqrt 97)/4}
      intro h
      by_cases h2 : x ≤ -3
      · -- Case x ≤ -3
        rw [abs_of_nonneg (show x^2 - 3 * x + 2 ≥ 0 by nlinarith), abs_of_nonneg (show x^2 + 2 * x - 3 ≥ 0 by nlinarith)] at h
        nlinarith [Real.sqrt_pos.mpr (show (97 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (97 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num : (0 : ℝ) ≤ (97 : ℝ)), sq_nonneg (x - (1 + Real.sqrt 97)/4), sq_nonneg (x - (1 - Real.sqrt 97)/4)]
      · -- Case -3 < x ≤ 1
        by_cases h3 : x ≤ 1
        · -- Case -3 < x ≤ 1
          rw [abs_of_nonneg (show x^2 - 3 * x + 2 ≥ 0 by nlinarith), abs_of_nonpos (show x^2 + 2 * x - 3 ≤ 0 by nlinarith)] at h
          have h4 : x = -6/5 := by linarith
          rw [h4]
          norm_num
        · -- Case 1 < x ≤ 2
          by_cases h4 : x ≤ 2
          · -- Case 1 < x ≤ 2
            rw [abs_of_nonpos (show x^2 - 3 * x + 2 ≤ 0 by nlinarith), abs_of_nonneg (show x^2 + 2 * x - 3 ≥ 0 by nlinarith)] at h
            nlinarith [Real.sqrt_pos.mpr (show (97 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num), sq_nonneg (x - 16/5)]
          · -- Case x > 2
            rw [abs_of_nonneg (show x^2 - 3 * x + 2 ≥ 0 by nlinarith), abs_of_nonneg (show x^2 + 2 * x - 3 ≥ 0 by nlinarith)] at h
            have h5 : 2 * x ^ 2 - x - 12 = 0 := by nlinarith
            have h6 : (x - (1 + Real.sqrt 97)/4) * (x - (1 - Real.sqrt 97)/4) = 0 := by
              nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
            cases' (mul_eq_zero.mp h6) with h7 h8
            · -- Assume x - (1 + Real.sqrt 97)/4 = 0
              have h9 : x = (1 + Real.sqrt 97)/4 := by linarith
              rw [h9]
              all_goals norm_num
            · -- Assume x - (1 - Real.sqrt 97)/4 = 0
              nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
    · -- Assume x ∈ {-6/5, (1 + Real.sqrt 97)/4}, prove abs (x ^ 2 - 3 * x + 2) + abs (x ^ 2 + 2 * x - 3) = 11
      rintro (rfl | rfl)
      · -- When x = -6/5
        norm_num [abs_of_nonneg, abs_of_nonpos]
      · -- When x = (1 + Real.sqrt 97)/4
        have h7 : ((1 + Real.sqrt 97)/4 : ℝ) ^ 2 - 3 * ((1 + Real.sqrt 97)/4 : ℝ) + 2 ≥ 0 := by
          nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
        have h8 : ((1 + Real.sqrt 97)/4 : ℝ) ^ 2 + 2 * ((1 + Real.sqrt 97)/4 : ℝ) - 3 ≥ 0 := by
          nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
        rw [abs_of_nonneg h7, abs_of_nonneg h8]
        nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
  rw [h1]
  rw [finsum_mem_pair (by
    nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
  )]
  all_goals
    ring_nf
    <;> nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]