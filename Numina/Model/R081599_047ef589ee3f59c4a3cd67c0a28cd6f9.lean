import Mathlib

open Real

theorem algebra_328448 : ⌊(sqrt 14 + 2) / (sqrt 14 - 2)⌋ = 3 := by
  have h1 : sqrt 14 > 2 := by
    have h4 : 2 < sqrt 14 := by
      rw [Real.lt_sqrt] <;> norm_num
    linarith
  have h3 : sqrt 14 - 2 > 0 := by
    linarith
  have h4 : 3 < (sqrt 14 + 2) / (sqrt 14 - 2) := by
    have h5 : sqrt 14 + 2 > 3 * (sqrt 14 - 2) := by
      -- Solve using 'nlinarith' (atured nonlinear arithmetic solver
      nlinarith [Real.sqrt_nonneg 14, Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ 14 by norm_num), show (2 : ℝ) < sqrt 14 by
        rw [Real.lt_sqrt] <;> norm_num
        ]
    apply (lt_div_iff₀' (by nlinarith)).mpr
    linarith
  have h6 : (sqrt 14 + 2) / (sqrt 14 - 2) < 4 := by
    have h7 : sqrt 14 + 2 < 4 * (sqrt 14 - 2) := by
      -- Let me use 'nlinarith' to solve the inequality (again)
      nlinarith [Real.sqrt_nonneg 14, Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ 14 by norm_num), show (2 : ℝ) < sqrt 14 by
        rw [Real.lt_sqrt] <;> norm_num
        ]
    apply (div_lt_iff₀' (by nlinarith)).mpr
    linarith
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> (try linarith)
  all_goals try norm_num
  all_goals try linarith
  all_goals try norm_num
  all_goals try linarith
  all_goals try norm_num
  all_goals try linarith
  all_goals try norm_num
  all_goals try linarith
  all_goals try norm_num
  all_goals try linarith