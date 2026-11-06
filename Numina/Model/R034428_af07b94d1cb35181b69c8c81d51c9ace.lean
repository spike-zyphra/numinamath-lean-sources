import Mathlib

theorem algebra_260925 : (Real.sqrt (25 * Real.sqrt 7 - 27 * Real.sqrt 6) - Real.sqrt (17 * Real.sqrt 5 - 38)) < 0 := by

  have h1 : 0 < (25 * Real.sqrt 7 - 27 * Real.sqrt 6 : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num),
            Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num),
            sq_nonneg (Real.sqrt 7 - Real.sqrt 6),
            Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num),
            Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num),
            Real.sqrt_nonneg 7, Real.sqrt_nonneg 6,
            mul_nonneg (Real.sqrt_nonneg 7) (Real.sqrt_nonneg 6)]

  have h2 : 0 < (17 * Real.sqrt 5 - 38 : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num),
            Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num),
            Real.sqrt_nonneg 5]

  have h3 : Real.sqrt (25 * Real.sqrt 7 - 27 * Real.sqrt 6) < Real.sqrt (17 * Real.sqrt 5 - 38) := by
    apply Real.sqrt_lt_sqrt
    all_goals
    nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num),
          Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num),
          Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num),
          sq_nonneg (Real.sqrt 7 - Real.sqrt 6),
          sq_nonneg (Real.sqrt 5 - 2),
          sq_nonneg (Real.sqrt 7 - Real.sqrt 5),
          sq_nonneg (Real.sqrt 6 - 2),
          Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num),
          Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num),
          Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num),
          mul_nonneg (Real.sqrt_nonneg 7) (Real.sqrt_nonneg 6),
          mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 6),
          mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 7),
          Real.sqrt_nonneg 7, Real.sqrt_nonneg 6, Real.sqrt_nonneg 5
        ]

  linarith [h3]