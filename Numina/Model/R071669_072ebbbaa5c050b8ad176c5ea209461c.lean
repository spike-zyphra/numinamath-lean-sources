import Mathlib

theorem algebra_10665 :
    Set.ncard {x : ℝ | abs (x^2 - 3 * x + 2) + abs (x^2 + 2 * x - 3) = 11} = 2 := by
  have h1 : {x : ℝ | abs (x^2 - 3 * x + 2) + abs (x^2 + 2 * x - 3) = 11} = 
          { (1 + Real.sqrt 97) / 4, (-6 / 5 : ℝ) } := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Forward implication: if x is a solution, then it is one of the two numbers.
      intro h
      by_cases h1 : x ≥ 2
      · -- Case 1: x ≥ 2
        rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)] at h
        have h2 : 2 * x^2 - x - 12 = 0 := by nlinarith
        have h3 : (x - (1 + Real.sqrt 97)/4) * (x - (1 - Real.sqrt 97)/4) = 0 := by
          nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (97 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num)]
        cases' (mul_eq_zero.mp h3) with h4 h5
        · -- Case where x = (1 + sqrt 97)/4
          have hx1 : x = (1 + Real.sqrt 97)/4 := by
            linarith
          left
          exact hx1
        · -- Case x = (1 - sqrt 97)/4
          have hx2 : x = (1 - Real.sqrt 97)/4 := by
            linarith
          nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (97 : ℝ) by norm_num)]
      · -- Case 2: x < 2
        by_cases h2 : x ≥ 1
        · -- Case 2a: 1 ≤ x < 2
          rw [abs_of_nonpos (by nlinarith), abs_of_nonneg (by nlinarith)] at h
          have h3 : 5 * x = 16 := by nlinarith
          nlinarith
        · -- Case 2b: x < 1
          by_cases h3 : x ≥ -3
          · -- Case 2b1: -3 ≤ x < 1
            rw [abs_of_nonneg (by nlinarith), abs_of_nonpos (by nlinarith)] at h
            have hx1 : x = (-6 / 5 : ℝ) := by
              nlinarith
            right
            exact hx1
          · -- Case 2b2: x < -3
            rw [abs_of_nonneg (by nlinarith), abs_of_nonneg (by nlinarith)] at h
            nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (97 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num)]
    · -- Backward implication: the two numbers satisfy the equation.
      rintro (rfl | rfl)
      · -- Check first solution
        have h1 : ( (1 + Real.sqrt 97)/4 : ℝ) ≥ 2 := by
          nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (97 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num)]
        rw [abs_of_nonneg (by nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (97 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num)]), 
            abs_of_nonneg (by nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (97 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num)])] 
        nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (97 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num)]
      · -- Check second solution
        have h2 : (-6 / 5 : ℝ) ≥ -3 := by norm_num
        rw [abs_of_nonneg (by nlinarith), abs_of_nonpos (by nlinarith)]
        nlinarith
  rw [h1]
  rw [Set.ncard_pair (by 
    intro h
    have h1 : (1 + Real.sqrt 97) / 4 = (-6 / 5 : ℝ) := h
    nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (97 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 97 by norm_num)]
  )]
  all_goals norm_num