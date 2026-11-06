import Mathlib

theorem algebra_15272 (a : ℝ) (ha : 0 < a ∧ a ≠ 1) :
    1 / Real.logb 2 a + 1 / Real.logb 3 a + 1 / Real.logb 4 a = 1 ↔ a = 24 := by
  constructor
  · -- Proof forward if the equation holds then a = 24
    intro h
    have h1 : Real.logb 2 a = Real.log a / Real.log (2 : ℝ) := by
      field_simp [Real.logb]
    have h2 : Real.logb 3 a = Real.log a / Real.log (3 : ℝ) := by
      field_simp [Real.logb]
    have h3 : Real.logb 4 a = Real.log a / Real.log (4 : ℝ) := by
      field_simp [Real.logb]
    rw [h1] at h
    rw [h2] at h
    rw [h3] at h
    have h4 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
      calc
        Real.log (4 : ℝ) = Real.log (2 ^ 2) := by norm_num
        _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]
    rw [h4] at h
    have h5 : Real.log (24 : ℝ) = 3 * Real.log (2 : ℝ) + Real.log (3 : ℝ) := by
      calc
        Real.log (24 : ℝ) = Real.log (8 * 3) := by norm_num
        _ = Real.log (8 : ℝ) + Real.log (3 : ℝ) := by rw [Real.log_mul (by norm_num) (by norm_num)]
        _ = Real.log (2 ^ 3) + Real.log (3 : ℝ) := by norm_num
        _ = 3 * Real.log (2 : ℝ) + Real.log (3 : ℝ) := by simp [Real.log_pow]
    have h6 : Real.log a = 3 * Real.log (2 : ℝ) + Real.log (3 : ℝ) := by
      have h7 : Real.log a ≠ 0 := by
        have ha' : a > 0 := ha.1
        have ha1' : a ≠ 1 := ha.2
        exact Real.log_ne_zero_of_pos_of_ne_one ha' ha1'
      field_simp [h7] at h ⊢
      nlinarith
    have h7 : Real.log a = Real.log (24 : ℝ) := by
      linarith [h5, h6]
    have h8 : a = (24 : ℝ) := by
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr ha.1) (Set.mem_Ioi.mpr (show (24 : ℝ) > 0 by norm_num)) h7
    linarith
  · -- Proof back if a = 24 then the equation holds
    intro h
    rw [h]
    have h1 : Real.logb (2 : ℝ) (24 : ℝ) = Real.log (24 : ℝ) / Real.log (2 : ℝ) := by
      field_simp [Real.logb]
    have h2 : Real.logb (3 : ℝ) (24 : ℝ) = Real.log (24 : ℝ) / Real.log (3 : ℝ) := by
      field_simp [Real.logb]
    have h3 : Real.logb (4 : ℝ) (24 : ℝ) = Real.log (24 : ℝ) / Real.log (4 : ℝ) := by
      field_simp [Real.logb]
    have h4 : Real.log (24 : ℝ) = 3 * Real.log (2 : ℝ) + Real.log (3 : ℝ) := by
      calc
        Real.log (24 : ℝ) = Real.log (8 * 3) := by norm_num
        _ = Real.log (8 : ℝ) + Real.log (3 : ℝ) := by rw [Real.log_mul (by norm_num) (by norm_num)]
        _ = Real.log (2 ^ 3) + Real.log (3 : ℝ) := by norm_num
        _ = 3 * Real.log (2 : ℝ) + Real.log (3 : ℝ) := by simp [Real.log_pow]
    have h5 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
      calc
        Real.log (4 : ℝ) = Real.log (2 ^ 2) := by norm_num
        _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]
    rw [h1, h2, h3, h4, h5]
    have h6 : Real.log (24 : ℝ) ≠ 0 := by
      have h7 : Real.log (24 : ℝ) > 0 := by
        apply Real.log_pos
        all_goals norm_num
      linarith
    field_simp [h6]
    <;> nlinarith