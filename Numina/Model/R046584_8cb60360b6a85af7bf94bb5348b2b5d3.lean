import Mathlib

theorem algebra_315617 : {x : ℝ | abs (x ^ 2 - 3 * x + 2) + abs (x ^ 2 + 2 * x - 3) = 11}.ncard = 2 := by
  have h1 : {x : ℝ | abs (x ^ 2 - 3 * x + 2) + abs (x ^ 2 + 2 * x - 3) = 11} = {-6/5, (1 + Real.sqrt 97)/4} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume abs (x ^ 2 - 3 * x + 2) + abs (x ^ 2 + 2 * x - 3) = 11, prove x ∈ {-6/5, (1 + Real.sqrt 97)/4}
      intro h
      by_cases h2 : x ≤ -3
      · -- Case x ≤ -3
        rw [abs_of_nonneg (show x ^ 2 - 3 * x + 2 ≥ 0 by nlinarith), abs_of_nonneg (show x ^ 2 + 2 * x - 3 ≥ 0 by nlinarith)] at h
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 97 by norm_num : (0 : ℝ) < 97), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num : (0 : ℝ) ≤ 97)]
      · -- Case -3 < x ≤ 1
        by_cases h3 : x ≤ 1
        · -- Case -3 < x ≤ 1
          rw [abs_of_nonneg (show x ^ 2 - 3 * x + 2 ≥ 0 by nlinarith), abs_of_nonpos (show x ^ 2 + 2 * x - 3 ≤ 0 by nlinarith)] at h
          have h4 : x = -6/5 := by linarith
          left
          linarith
        · -- Case 1 < x ≤ 2
          by_cases h4 : x ≤ 2
          · -- Case 1 < x ≤ 2
            rw [abs_of_nonpos (show x ^ 2 - 3 * x + 2 ≤ 0 by nlinarith), abs_of_nonneg (show x ^ 2 + 2 * x - 3 ≥ 0 by nlinarith)] at h
            nlinarith
          · -- Case x > 2
            rw [abs_of_nonneg (show x ^ 2 - 3 * x + 2 ≥ 0 by nlinarith), abs_of_nonneg (show x ^ 2 + 2 * x - 3 ≥ 0 by nlinarith)] at h
            have h5 : 2 * x ^ 2 - x - 12 = 0 := by nlinarith
            have h8 : (x - (1 + Real.sqrt 97) / 4) * (x - (1 - Real.sqrt 97) / 4) = 0 := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 97 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num)]
            cases' (mul_eq_zero.mp h8) with h9 h10
            · -- Case x = (1 + Real.sqrt 97) / 4
              have h11 : x = (1 + Real.sqrt 97) / 4 := by linarith
              right
              linarith
            · -- Case x = (1 - Real.sqrt 97) / 4
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 97 by norm_num : (0 : ℝ) < 97), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num : (0 : ℝ) ≤ 97)]
    · -- Assume x ∈ {-6/5, (1 + Real.sqrt 97)/4}, prove abs (x ^ 2 - 3 * x + 2) + abs (x ^ 2 + 2 * x - 3) = 11
      rintro (h | h)
      · -- Case x = -6/5
        rw [h]
        norm_num [abs_of_nonneg, abs_of_nonpos]
      · -- Case x = (1 + Real.sqrt 97) / 4
        rw [h]
        have h2 : ((1 + Real.sqrt 97) / 4 : ℝ) ^ 2 - 3 * ((1 + Real.sqrt 97) / 4 : ℝ) + 2 ≥ 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 97 by norm_num : (0 : ℝ) < 97), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num : (0 : ℝ) ≤ 97)]
        have h3 : ((1 + Real.sqrt 97) / 4 : ℝ) ^ 2 + 2 * ((1 + Real.sqrt 97) / 4 : ℝ) - 3 ≥ 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 97 by norm_num : (0 : ℝ) < 97), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num : (0 : ℝ) ≤ 97)]
        rw [abs_of_nonneg h2, abs_of_nonneg h3]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 97 by norm_num : (0 : ℝ) < 97), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num : (0 : ℝ) ≤ 97)]
  rw [h1]
  rw [Set.ncard_pair]
  all_goals
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 97 by norm_num : (0 : ℝ) < 97), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num : (0 : ℝ) ≤ 97)]