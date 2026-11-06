import Mathlib

theorem algebra_187733 (x : ℝ) (hx : 3 * x - 11 > 0 ∧ x - 27 > 0) :
    Real.logb 5 (3 * x - 11) + Real.logb 5 (x - 27) = 3 + Real.logb 5 8 ↔ x = 37 := by
  constructor
  · -- Assume the equation holds, prove x = 37
    intro h_eq
    rcases hx with ⟨h1, h2⟩
    have h3 : Real.logb 5 (3 * x - 11) + Real.logb 5 (x - 27) = Real.logb 5 ((3 * x - 11) * (x - 27)) := by
      rw [← Real.logb_mul (by linarith) (by linarith)]
    rw [h3] at h_eq
    have h4 : (3 : ℝ) + Real.logb 5 8 = Real.logb 5 (125 * 8) := by
      have h5 : Real.logb 5 (125 * 8) = Real.logb 5 (125) + Real.logb 5 (8) := by
        rw [Real.logb_mul (by norm_num) (by norm_num)]
      have h6 : Real.logb 5 (125 : ℝ) = 3 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h5, h6]
    rw [h4] at h_eq
    have h7 : (3 * x - 11 : ℝ) * (x - 27) = (125 * 8 : ℝ) := by
      have h8 : Real.logb 5 ((3 * x - 11 : ℝ) * (x - 27)) = Real.logb 5 (125 * 8) := h_eq
      have h9 : (3 * x - 11 : ℝ) * (x - 27) > 0 := by
        positivity
      have h10 : (125 * 8 : ℝ) > 0 := by
        norm_num
      have h11 : (3 * x - 11 : ℝ) * (x - 27) = (125 * 8 : ℝ) := by
        apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h9) (Set.mem_Ioi.mpr h10) h8
      linarith
    have h8 : (3 * x - 11 : ℝ) * (x - 27) = (1000 : ℝ) := by 
      linarith
    have h9 : 3 * x ^ 2 - 92 * x - 703 = 0 := by 
      nlinarith
    have h10 : (x - 37 : ℝ) * (3 * x + 19) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp h10) with h11 h12
    · 
      linarith
    · 
      have h13 : x < (0 : ℝ) := by 
        nlinarith
      nlinarith
  · -- Assume x = 37, prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : (3 * (37 : ℝ) - 11 : ℝ) = (100 : ℝ) := by norm_num
    have h2 : (37 : ℝ) - 27 = (10 : ℝ) := by norm_num
    rw [h1, h2]
    have h3 : Real.logb 5 (100 : ℝ) + Real.logb 5 (10 : ℝ) = Real.logb 5 (100 * 10 : ℝ) := by 
      rw [← Real.logb_mul (by norm_num) (by norm_num)]
    have h5 : (100 * 10 : ℝ) = (125 * 8 : ℝ) := by norm_num 
    have h6 : Real.logb 5 (100 * 10 : ℝ) = Real.logb 5 (125 * 8 : ℝ) := by 
      rw [h5]
    have h7 : Real.logb 5 (125 * 8 : ℝ) = Real.logb 5 (125 : ℝ) + Real.logb 5 (8 : ℝ) := by 
      rw [Real.logb_mul (by norm_num) (by norm_num)]
    have h8 : Real.logb 5 (125 : ℝ) = (3 : ℝ) := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
    rw [h3, h6, h7, h8]
    all_goals norm_num