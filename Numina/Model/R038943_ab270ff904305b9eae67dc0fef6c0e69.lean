import Mathlib

open Real

theorem algebra_20480 :
    IsGreatest {x | ∃ a b c : ℝ, 0 ≤ c ∧ c ≤ b ∧ b ≤ a ∧ a + b = 16 ∧ x = Real.sqrt (c * (b - c)) + Real.sqrt (c * (a - c))} 8 := by
  constructor
  · -- Show 8 is in the set.
    use 8, 8, 4
    constructor
    · norm_num  -- Show 0 ≤ c
    constructor
    · norm_num  -- Show c ≤ b
    constructor
    · norm_num  -- Show b ≤ a
    constructor
    · norm_num  -- Show a + b = 16
    have h1 : Real.sqrt (4 * (8 - 4)) + Real.sqrt (4 * (8 - 4)) = 8 := by
      have h2 : Real.sqrt (4 * (8 - 4)) = 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h2]
      all_goals norm_num
    linarith [h1]
  · -- Show x ≤ 8 for all x in the set
    intro x hx
    rcases hx with ⟨a, b, c, hc1, h1, h2, heq, hx⟩
    have h3 : a = 16 - b := by linarith
    have h4 : c ≤ b := h1
    have h5 : 0 ≤ c := hc1
    have h6 : b ≤ a := h2
    have h7 : a + b = 16 := heq
    have h8 : 0 ≤ b - c := by nlinarith
    have h9 : 0 ≤ a - c := by nlinarith
    have h10 : Real.sqrt (c * (b - c)) + Real.sqrt (c * (a - c)) ≤ 8 := by
      nlinarith [sq_nonneg (Real.sqrt (c * (b - c)) - 4), sq_nonneg (Real.sqrt (c * (a - c)) - 4),
          Real.sqrt_nonneg (c * (b - c)), Real.sqrt_nonneg (c * (a - c)), 
          mul_nonneg (Real.sqrt_nonneg (c * (b - c))) (Real.sqrt_nonneg (c * (a - c))), 
          sq_nonneg (c - 4), 
          Real.sq_sqrt (show 0 ≤ c * (b - c) by nlinarith), 
          Real.sq_sqrt (show 0 ≤ c * (a - c) by nlinarith), 
          mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ b - c by linarith), 
          mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ a - c by linarith), 
          h8, h9 
        ]
    linarith [h10, hx]