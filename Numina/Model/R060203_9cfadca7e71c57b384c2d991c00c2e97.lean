import Mathlib

theorem algebra_153601 (x : ℝ) (hx : x > 0) :
    (1 / 12) * Real.logb 10 x ^ 2 = (1 / 3) - (1 / 4) * Real.logb 10 x ↔
    x = 0.0001 ∨ x = 10 := by
  constructor
  · -- Forward: assuming the equation holds, prove the root is one of the two solutions.
    intro h_eq
    have eq1 : (Real.logb 10 x) ^ 2 + 3 * (Real.logb 10 x) - 4 = 0 := by
      nlinarith
    have h_eq2 : (Real.logb 10 x + 4) * (Real.logb 10 x - 1) = 0 := by
      nlinarith
      -- factored form of the quadratic
    cases' (mul_eq_zero.mp h_eq2) with h_eq3 h_eq4
    · -- Case: (Real.logb 10 x + 4) = 0
      have h_eq5 : Real.logb 10 x = -4 := by linarith
      have h_eq6 : x = (10 : ℝ) ^ (-4 : ℝ) := by 
        rw [Real.logb_eq_iff_rpow_eq] at h_eq5
        · 
          linarith 
        all_goals 
          linarith
        <;> norm_num
        <;> linarith 
      have h_eq7 : x = (0.0001 : ℝ) := by 
        rw [h_eq6]
        norm_num
      left
      linarith
    · -- Case: (Real.logb 10 x - 1) = 0
      have h_eq8 : Real.logb 10 x = 1 := by linarith
      have h_eq9 : x = (10 : ℝ) ^ (1 : ℝ) := by
        rw [Real.logb_eq_iff_rpow_eq] at h_eq8
        · 
          linarith 
        all_goals 
          linarith 
        <;> norm_num
        <;> linarith 
      have h_eq10 : x = (10 : ℝ) := by
        rw [h_eq9]
        norm_num
      right
      linarith 
  · -- Backward: showing each solution satisfies the equation.
    rintro (h_eq | h_eq)
    · -- x = 0.0001
      rw [h_eq]
      have h_eq1 : Real.logb 10 (0.0001 : ℝ) = -4 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h_eq1]
      norm_num 
    · -- x = 10
      rw [h_eq]
      have h_eq2 : Real.logb 10 (10 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
      rw [h_eq2]
      norm_num