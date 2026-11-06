import Mathlib

theorem algebra_188107 {a M : ℝ} (ha : 0 < a ∧ a ≠ 1) (hM : 0 < M) (hM1 : Real.logb 10 M = 1 / a) :
    Real.logb 10 (1 / M) = -1 / a := by
  have h1 : Real.logb 10 (1 / M) = - Real.logb 10 M := by 
    rw [show Real.logb 10 (1 / M) = Real.logb 10 1 - Real.logb 10 M by 
      field_simp [Real.logb_div] ]
    have h_logb_one : Real.logb 10 1 = 0 := by 
      norm_num [Real.logb_one]
    rw [h_logb_one]
    all_goals linarith
  rw [h1]
  rw [hM1]
  <;> ring