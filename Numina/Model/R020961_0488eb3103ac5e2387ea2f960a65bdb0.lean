import Mathlib

theorem algebra_187789 (x : ℝ) (hx : 0 < x) :
    Real.logb 0.5 (4 * x) ^ 2 + Real.logb 2 (x ^ 2 / 8) = 8 ↔
    x = 1 / 128 ∨ x = 2 := by
  constructor
  · -- Forward: if the equation holds, then x is one of the solutions
    intro h_eq
    have h1 : Real.logb 0.5 (4 * x) = - (Real.logb 2 (4 * x) ) := by
      have h2 : Real.logb 0.5 (4 * x) = Real.logb 2 (4 * x) / Real.logb 2 (0.5 : ℝ) := by 
        field_simp [Real.logb]
      have h3 : Real.logb 2 (0.5 : ℝ) = -1 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h2, h3]
      all_goals ring
    have h4 : Real.logb 2 (4 * x) = Real.logb 2 4 + Real.logb 2 x := by 
      rw [Real.logb_mul (by norm_num) (by linarith)]
    have h5 : Real.logb 2 (4 : ℝ) = 2 := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    have h6 : Real.logb 2 (4 * x) = 2 + Real.logb 2 x := by 
      rw [h4, h5]
    have h7 : Real.logb 0.5 (4 * x) = - (2 + Real.logb 2 x) := by 
      rw [h1, h6]
    have h8 : Real.logb 2 (x ^ 2 / 8) = 2 * Real.logb 2 x - 3 := by 
      have h9 : Real.logb 2 (x ^ 2 / 8) = Real.logb 2 (x ^ 2) - Real.logb 2 (8 : ℝ) := by 
        rw [Real.logb_div (by positivity) (by positivity)]
      have h10 : Real.logb 2 (x ^ 2) = 2 * Real.logb 2 x := by 
        simp [Real.logb_pow]
      have h11 : Real.logb 2 (8 : ℝ) = 3 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h9, h10, h11]
    rw [h7] at h_eq
    rw [h8] at h_eq 
    have h9 : (Real.logb 2 x) ^ 2 + 6 * (Real.logb 2 x) - 7 = 0 := by
      nlinarith 
    have h10 : (Real.logb 2 x + 7) * (Real.logb 2 x - 1) = 0 := by 
      nlinarith [h9]
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- Case h11: Real.logb 2 x + 7 = 0 
      have h13 : Real.logb 2 x = -7 := by 
        linarith 
      have h14 : x = (1 / 128 : ℝ) := by
        have h15 : x = (2 : ℝ) ^ (Real.logb 2 x : ℝ) := by 
          field_simp 
        rw [h13] at h15 
        have h16 : x = (2 : ℝ) ^ (-7 : ℝ) := by 
          linarith 
        rw [h16]
        norm_num 
      left 
      linarith [h14]
    · -- Case h12: Real.logb 2 x - 1 = 0 
      have h13 : Real.logb 2 x = 1 := by 
        linarith 
      have h14 : x = (2 : ℝ) := by 
        have h15 : x = (2 : ℝ) ^ (Real.logb 2 x : ℝ) := by 
          field_simp 
        rw [h13] at h15 
        have h16 : x = (2 : ℝ) ^ (1 : ℝ) := by 
          linarith 
        rw [h16]
        all_goals norm_num 
      right 
      linarith [h14]
  · -- Reverse: if x is one of the solutions, then the equation holds 
    rintro (h | h)
    · -- Case x = 1/128 
      rw [h]
      have h7 : Real.logb 0.5 (4 * (1 / 128 : ℝ) ) = - (Real.logb 2 (4 * (1 / 128 : ℝ)) ) := by 
        have h2 : Real.logb 0.5 (4 * (1 / 128 : ℝ)) = Real.logb 2 (4 * (1 / 128 : ℝ)) / Real.logb 2 (0.5 : ℝ) := by 
          field_simp [Real.logb]
        have h3 : Real.logb 2 (0.5 : ℝ) = -1 := by 
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
        rw [h2, h3]
        all_goals ring 
      have h8 : Real.logb 2 (4 * (1 / 128 : ℝ) ) = -5 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      have h9 : Real.logb 2 ((1 / 128 : ℝ) ^ 2 / 8) = -17 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      rw [h7, h8, h9]
      all_goals norm_num 
    · -- Case x = 2 
      rw [h]
      have h7 : Real.logb 0.5 (4 * (2 : ℝ)) = - (Real.logb 2 (4 * (2 : ℝ)) ) := by 
        have h2 : Real.logb 0.5 (4 * (2 : ℝ)) = Real.logb 2 (4 * (2 : ℝ)) / Real.logb 2 (0.5 : ℝ) := by 
          field_simp [Real.logb]
        have h3 : Real.logb 2 (0.5 : ℝ) = -1 := by 
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
        rw [h2, h3]
        all_goals ring 
      have h8 : Real.logb 2 (4 * (2 : ℝ)) = 3 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      have h9 : Real.logb 2 ((2 : ℝ) ^ 2 / 8) = -1 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      rw [h7, h8, h9]
      all_goals norm_num