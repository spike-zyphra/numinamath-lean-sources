import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_224760 (x : ℝ) :
  (x + 1)^3 * (x^3 + 5 * x) < 10 * (x + 1)^2 + 8 ↔ x ∈ Ioo (-2) 1 := by 
  constructor
  · -- Assume the inequality holds, prove x ∈ (-2, 1)
    intro h 
    have h1 : -2 < x := by
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - x), sq_nonneg ((x + 1) ^ 2 - 1),
          sq_nonneg (x * (x - 1)), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg ((x + 2) * (x - 1)), 
          sq_pos_of_pos (show (1 : ℝ) > 0 by norm_num)
        ]
    have h2 : x < 1 := by 
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - x), sq_nonneg ((x + 1) ^ 2 - 1),
          sq_nonneg (x * (x - 1)), sq_nonneg ((x + 1) * (x - 1)), sq_nonneg ((x + 2) * (x - 1)), 
          sq_pos_of_pos (show (1 : ℝ) > 0 by norm_num)
        ]
    exact ⟨h1, h2⟩
  · -- Assume x ∈ (-2, 1), prove the inequality
    rintro ⟨h1, h2⟩
    have h3 : -2 < x := h1
    have h4 : x < 1 := h2
    have h5 : (x + 1) ^ 3 * (x ^ 3 + 5 * x) - (10 * (x + 1) ^ 2 + 8) < (0 : ℝ) := by 
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x * (x - 1)), 
          sq_nonneg ((x + 1) * (x - 1)), sq_nonneg ((x + 2) * (x - 1)), 
          sq_nonneg (x * (x + 1)), sq_nonneg ((x + 2) * (x + 1)), 
          sq_nonneg ((x - 1) * (x + 1)), sq_nonneg ((x ^ 2) * (x + 2)), 
          sq_nonneg (x + 1), 
          mul_pos (sub_pos.mpr (show -2 < x by linarith)) (sub_pos.mpr (show x < (1 : ℝ) by linarith)), 
          mul_pos (sub_pos.mpr (show -2 < x by linarith)) (sub_pos.mpr (show x < (1 : ℝ) by linarith))
        ]
    linarith