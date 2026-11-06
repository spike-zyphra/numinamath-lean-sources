import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_325376 (a : ℝ) :
  a < 9 * a^3 - 11 * a ∧ 9 * a^3 - 11 * a < abs a ↔
  -2 * sqrt 3 / 3 < a ∧ a < -sqrt 10 / 3 := by
  constructor
  · -- Assume the inequalities hold
    intro h
    rcases h with ⟨h1, h2⟩
    by_cases h5 : a ≥ 0
    · -- a ≥ 0
      have h5a : abs a = a := abs_of_nonneg h5
      rw [h5a] at h2
      nlinarith [sq_nonneg (a ^ 2 - 4 / 3), sq_nonneg (a - 2 * sqrt 3 / 3), sq_nonneg (a + 2 * sqrt 3 / 3),
        Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0),
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0),
        Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num : (10 : ℝ) > 0),
        Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (10 : ℝ) ≥ 0)
      ]
    · -- a < 0
      have h5a : abs a = -a := abs_of_neg (lt_of_not_ge h5)
      rw [h5a] at h2
      constructor
      · -- Show that -2 * sqrt 3 / 3 < a
        nlinarith [sq_nonneg (a + 2 * sqrt 3 / 3), sq_nonneg (a + sqrt 10 / 3),
          Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0),
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0),
          Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num : (10 : ℝ) > 0),
          Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (10 : ℝ) ≥ 0),
          mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0)) (Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num : (10 : ℝ) > 0)), 
          sq_nonneg (a ^ 2)
        ]
      · -- Show that a < -sqrt 10 / 3
        nlinarith [sq_nonneg (a + sqrt 10 / 3), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0),
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0),
          Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num : (10 : ℝ) > 0),
          Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (10 : ℝ) ≥ 0),
          mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0)) (Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num : (10 : ℝ) > 0)), 
          sq_nonneg (a ^ 2)
        ]
  · -- Assume the bounds hold
    rintro ⟨h1, h2⟩
    have h3 : a < 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num : (10 : ℝ) > 0), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (10 : ℝ) ≥ 0), 
        h1, h2
      ]
    have h4 : abs a = -a := abs_of_neg h3
    constructor
    · -- Prove a < 9 * a^3 - 11 * a
      nlinarith [sq_nonneg (a + 2 * sqrt 3 / 3), sq_nonneg (a - 2 * sqrt 3 / 3), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num : (10 : ℝ) > 0), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (10 : ℝ) ≥ 0), 
        h1, h2, 
        mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0)) (Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num : (10 : ℝ) > 0)), 
        sq_nonneg (a ^ 2)
      ]
    · -- Prove 9 * a^3 - 11 * a < abs a
      rw [h4]
      nlinarith [sq_nonneg (a + sqrt 10 / 3), sq_nonneg (a - sqrt 10 / 3), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0),
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num : (10 : ℝ) > 0), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num : (10 : ℝ) ≥ 0), 
        h1, h2, 
        mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0)) (Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num : (10 : ℝ) > 0)), 
        sq_nonneg (a ^ 2)
      ]