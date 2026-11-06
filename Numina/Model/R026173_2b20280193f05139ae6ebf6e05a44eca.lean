import Mathlib

theorem algebra_230961 : {x : ℝ | abs (x^2 - 3 * x + 2) + abs (x^2 + 2 * x - 3) = 11}.encard = 2 := by

  have h1 : {x : ℝ | abs (x^2 - 3 * x + 2) + abs (x^2 + 2 * x - 3) = 11} = {(-6 / 5 : ℝ), (1 + Real.sqrt 97) / 4} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume h : abs (x^2 - 3 * x + 2) + abs (x^2 + 2 * x - 3) = 11, prove { (-6/5), (1 + sqrt 97)/4 }
      intro h
      by_cases h2 : x ≥ 2
      · -- Case x ≥ 2
        rw [abs_of_nonneg (show x ^ 2 - 3 * x + 2 ≥ 0 by nlinarith), abs_of_nonneg (show x ^ 2 + 2 * x - 3 ≥ 0 by nlinarith)] at h
        have h3 : 2 * x ^ 2 - x - 12 = 0 := by nlinarith
        have h4 : (x - (1 + Real.sqrt 97) / 4) * (x - (1 - Real.sqrt 97) / 4) = 0 := by
          nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
        cases' (mul_eq_zero.mp h4) with h5 h6
        · -- Case x = (1 + Real.sqrt 97) / 4
          right
          linarith
        · -- Case x = (1 - Real.sqrt 97) / 4
          nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
      by_cases h3 : x ≥ 1
      · -- Case 1 ≤ x < 2
        rw [abs_of_nonpos (show x ^ 2 - 3 * x + 2 ≤ 0 by nlinarith), abs_of_nonneg (show x ^ 2 + 2 * x - 3 ≥ 0 by nlinarith)] at h
        nlinarith
      by_cases h4 : x ≥ -3
      · -- Case -3 ≤ x < 1
        rw [abs_of_nonneg (show x ^ 2 - 3 * x + 2 ≥ 0 by nlinarith), abs_of_nonpos (show x ^ 2 + 2 * x - 3 ≤ 0 by nlinarith)] at h
        have h1 : x = (-6 / 5 : ℝ) := by nlinarith
        left
        linarith
      · -- Case x < -3
        rw [abs_of_nonneg (show x ^ 2 - 3 * x + 2 ≥ 0 by nlinarith), abs_of_nonneg (show x ^ 2 + 2 * x - 3 ≥ 0 by nlinarith)] at h
        nlinarith
    · -- Assume { (-6/5), (1 + sqrt 97)/4 }, prove h : abs (x^2 - 3 * x + 2) + abs (x^2 + 2 * x - 3) = 11
      rintro (h | h)
      · -- Case x = -6 / 5
        rw [h]
        norm_num [abs_of_nonneg, abs_of_nonpos]
      · -- Case x = (1 + Real.sqrt 97) / 4
        rw [h]
        have h2 : (1 + Real.sqrt 97) / 4 ≥ 2 := by
          nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
        rw [abs_of_nonneg (show ((1 + Real.sqrt 97) / 4 : ℝ) ^ 2 - 3 * ((1 + Real.sqrt 97) / 4) + 2 ≥ 0 by nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]), abs_of_nonneg (show ((1 + Real.sqrt 97) / 4 : ℝ) ^ 2 + 2 * ((1 + Real.sqrt 97) / 4) - 3 ≥ 0 by nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)])]
        nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]

  rw [h1]
  have h2 : (-6 / 5 : ℝ) ≠ (1 + Real.sqrt 97) / 4 := by
    nlinarith [Real.sqrt_nonneg 97, Real.sq_sqrt (show (0 : ℝ) ≤ (97 : ℝ) by norm_num)]
  rw [Set.encard_pair h2]
  all_goals norm_num