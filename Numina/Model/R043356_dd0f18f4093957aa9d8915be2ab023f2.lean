import Mathlib

theorem algebra_2393 : {x : ℝ | abs (x^2 - 1) = (x + 9 / 10) / 10}.encard = 2 := by
  have h1 : {x : ℝ | abs (x^2 - 1) = (x + 9 / 10) / 10} = { (1 + Real.sqrt 437) / 20, (-1 + Real.sqrt 365) / 20 } := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume abs (x^2 - 1) = (x + 9 / 10) / 10
      intro h
      by_cases h2 : x ^ 2 - 1 ≥ 0
      · -- abs (x ^ 2 - 1) = x ^ 2 - 1
        rw [abs_of_nonneg h2] at h
        -- Now solve the equation
        have h4 : 10 * (x ^ 2) - x - (10 + 0.9) = 0 := by
          nlinarith [h]
        have h5 : 10 * (x ^ 2) - x - (10 + (9 / 10)) = 0 := by
          ring_nf at h4 ⊢
          linarith
        -- Now need to solve a quadratic
        have h6 : (x - (1 + Real.sqrt 437) / 20) * (x - (1 - Real.sqrt 437) / 20) = 0 := by
          nlinarith [sq_nonneg (x - (1 / 20)), sq_nonneg (Real.sqrt 437), Real.sqrt_nonneg 437, Real.sq_sqrt (show (0 : ℝ) ≤ (437 : ℝ) by norm_num)]
        cases' (mul_eq_zero.mp h6) with h7 h8
        · -- Case where x = (1 + Real.sqrt 437) / 20
          left
          linarith
        · -- Case where x = (1 - Real.sqrt 437) / 20
          nlinarith [Real.sqrt_nonneg 437, Real.sq_sqrt (show (0 : ℝ) ≤ (437 : ℝ) by norm_num)]
      · -- Case where x^2 - 1 < 0
        rw [abs_of_neg (show x^2 - 1 < 0 by linarith)] at h
        -- Now solve the equation
        have h4 : 10 * (x ^ 2) + x - 9.1 = 0 := by
          nlinarith [h]
        have h5 : (x - (-1 + Real.sqrt 365) / 20) * (x - (-1 - Real.sqrt 365) / 20) = 0 := by
          nlinarith [sq_nonneg (x + (1 / 20)), sq_nonneg (Real.sqrt 365), Real.sqrt_nonneg 365, Real.sq_sqrt (show (0 : ℝ) ≤ (365 : ℝ) by norm_num)]
        cases' (mul_eq_zero.mp h5) with h7 h8
        · -- Case where x = (-1 + Real.sqrt 365) / 20
          right
          linarith
        · -- Case where x = (-1 - Real.sqrt 365) / 20
          nlinarith [Real.sqrt_nonneg 365, Real.sq_sqrt (show (0 : ℝ) ≤ (365 : ℝ) by norm_num)]
    · -- Assume x in { (1 + Real.sqrt 437) / 20, (-1 + Real.sqrt 365) / 20 }
      intro h
      rcases h with (h | h)
      · -- Case x = (1 + Real.sqrt 437) / 20
        rw [h]
        have h1 : ((1 + Real.sqrt 437) / 20 : ℝ) ^ 2 - 1 ≥ 0 := by
          nlinarith [Real.sqrt_nonneg 437, Real.sq_sqrt (show (0 : ℝ) ≤ (437 : ℝ) by norm_num)]
        rw [abs_of_nonneg h1]
        nlinarith [Real.sqrt_nonneg 437, Real.sq_sqrt (show (0 : ℝ) ≤ (437 : ℝ) by norm_num)]
      · -- Case x = (-1 + Real.sqrt 365) / 20
        rw [h]
        have h1 : ((-1 + Real.sqrt 365) / 20 : ℝ) ^ 2 - 1 < 0 := by
          nlinarith [Real.sqrt_nonneg 365, Real.sq_sqrt (show (0 : ℝ) ≤ (365 : ℝ) by norm_num)]
        rw [abs_of_neg h1]
        nlinarith [Real.sqrt_nonneg 365, Real.sq_sqrt (show (0 : ℝ) ≤ (365 : ℝ) by norm_num)]
  rw [h1]
  rw [Set.encard_pair]
  all_goals
    nlinarith [Real.sqrt_nonneg 437, Real.sqrt_nonneg 365, Real.sq_sqrt (show (0 : ℝ) ≤ (437 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (365 : ℝ) by norm_num), show (437 : ℝ) > (365 : ℝ) by norm_num]