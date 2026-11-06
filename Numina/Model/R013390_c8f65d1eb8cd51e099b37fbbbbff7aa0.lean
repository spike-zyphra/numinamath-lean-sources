import Mathlib

theorem algebra_150170 (x : ℝ) (hx : x > 0) :
    x ^ (Real.logb 2 (8 * x)) = x ^ 7 / 8 ↔ x = 2 ∨ x = 8 := by
  constructor
  · -- Forward implication: the equation implies the solutions
    intro h_eq
    have h1 : Real.logb 2 (8 * x) = 3 + Real.logb 2 x := by
      calc
        Real.logb 2 (8 * x) = Real.logb 2 8 + Real.logb 2 x := by
          rw [Real.logb_mul (by norm_num) (by linarith)]
        _ = Real.logb 2 (2 ^ 3) + Real.logb 2 x := by
          norm_num
        _ = 3 * Real.logb 2 2 + Real.logb 2 x := by
          simp [Real.logb_pow]
        _ = 3 + Real.logb 2 x := by
          simp [Real.logb_self_eq_one]
    have h2 : Real.logb 2 (x ^ (Real.logb 2 (8 * x))) = Real.logb 2 (x ^ 7 / 8) := by
      rw [h_eq]
    have h3 : Real.logb 2 (x ^ (Real.logb 2 (8 * x))) = Real.logb 2 (8 * x) * Real.logb 2 x := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals linarith
    have h4 : Real.logb 2 (x ^ 7 / 8) = 7 * Real.logb 2 x - 3 := by
      have h5 : Real.logb 2 (x ^ 7 / 8) = Real.logb 2 (x ^ 7) - Real.logb 2 (8 : ℝ) := by
        rw [Real.logb_div (by positivity) (by positivity)]
      have h6 : Real.logb 2 (x ^ 7) = 7 * Real.logb 2 x := by
        simp [Real.logb_pow]
      have h7 : Real.logb 2 (8 : ℝ) = 3 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        <;> linarith
      rw [h5, h6, h7]
    rw [h3, h4] at h2
    rw [h1] at h2
    have h5 : Real.logb 2 x ^ 2 - 4 * Real.logb 2 x + 3 = 0 := by
      nlinarith
    have h5a : (Real.logb 2 x - 1) * (Real.logb 2 x - 3) = 0 := by
      linarith [h5]
    cases' (mul_eq_zero.mp h5a) with h6 h7
    · -- Case where $\log_2(x) - 1 = 0$
      have h8 : Real.logb 2 x = 1 := by
        linarith
      have h9 : x = (2 : ℝ) := by
        have : x = 2 ^ (Real.logb 2 x) := by
          field_simp [Real.rpow_logb, hx]
        rw [h8] at this
        norm_num at this ⊢
        exact this
      left
      exact h9
    · -- Case where $\log_2(x) - 3 = 0$
      have h8 : Real.logb 2 x = 3 := by
        linarith
      have h9 : x = (8 : ℝ) := by
        have : x = 2 ^ (Real.logb 2 x) := by
          field_simp [Real.rpow_logb, hx]
        rw [h8] at this
        norm_num at this ⊢
        exact this
      right
      exact h9
  · -- Backward direction: if x = 2 ∨ x = 8 then the equation holds
    rintro (h_eq | h_eq)
    · -- Show that 2 is a solution
      rw [h_eq]
      have h3 : Real.logb (2 : ℝ) (8 * (2 : ℝ)) = (4 : ℝ) := by
        calc
          Real.logb (2 : ℝ) (8 * (2 : ℝ)) = Real.logb (2 : ℝ) (16 : ℝ) := by norm_num
          _ = 4 := by
            rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      norm_num [h3, Real.rpow_nat_cast, pow_succ, pow_zero]
    · -- Show that 8 is a solution
      rw [h_eq]
      have h1 : Real.logb (2 : ℝ) (8 * (8 : ℝ)) = (6 : ℝ) := by
        calc
          Real.logb (2 : ℝ) (8 * (8 : ℝ)) = Real.logb (2 : ℝ) (64 : ℝ) := by norm_num
          _ = (6 : ℝ) := by 
            rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      have eq2 : (8 : ℝ) ^ Real.logb (2 : ℝ) (8 * (8 : ℝ)) = (8 : ℝ) ^ (7 : ℕ) / (8 : ℝ) := by 
        rw [show Real.logb (2 : ℝ) (8 * (8 : ℝ)) = (6 : ℝ) by linarith [h1]]
        norm_num
      linarith [eq2]