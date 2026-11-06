import Mathlib

theorem algebra_310342 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) :
    1 / Real.logb 2 a + 1 / Real.logb 3 a + 1 / Real.logb 4 a = 1 ↔ a = 24 := by
  constructor
  · -- Assume the equation holds, prove a = 24
    intro h
    have ha1 : a > 0 := ha.1
    have ha2 : a ≠ 1 := ha.2
    have h1 : 1 / Real.logb 2 a + 1 / Real.logb 3 a + 1 / Real.logb 4 a = 1 := h
    have h2 : Real.logb 2 a = Real.log a / Real.log 2 := by
      field_simp [Real.logb]
    have h3 : Real.logb 3 a = Real.log a / Real.log 3 := by
      field_simp [Real.logb]
    have h4 : Real.logb 4 a = Real.log a / Real.log 4 := by
      field_simp [Real.logb]
    rw [h2] at h1
    rw [h3] at h1
    rw [h4] at h1
    have h5 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
      calc
        Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]
    have h6 : Real.log 2 + Real.log 3 + Real.log 4 = Real.log (24 : ℝ) := by
      have h7 : Real.log 2 + Real.log 3 + Real.log 4 = Real.log (2 * 3 * 4) := by
        have h8 : Real.log (2 * 3 * 4) = Real.log (2 * 3) + Real.log (4 : ℝ) := by
          rw [← Real.log_mul (by norm_num) (by norm_num)]
        have h9 : Real.log (2 * 3) = Real.log (2 : ℝ) + Real.log (3 : ℝ) := by
          rw [Real.log_mul (by norm_num) (by norm_num)]
        linarith [h8, h9]
      have h11 : Real.log (2 * 3 * 4) = Real.log (24 : ℝ) := by
        norm_num
      linarith [h7, h11]
    have h9 : Real.log a ≠ 0 := by
      have ha3 : a > 0 := ha1
      have ha4 : a ≠ 1 := ha2
      exact Real.log_ne_zero_of_pos_of_ne_one ha3 ha4
    have h10 : Real.log 2 + Real.log 3 + Real.log 4 = Real.log a := by
      have h8 : Real.log a ≠ 0 := h9
      field_simp [h8, h5] at h1
      linarith
    have h11 : Real.log 24 = Real.log a := by
      linarith [h6, h10]
    have h12 : a = 24 := by
      have h14 : Real.log a = Real.log 24 := by
        linarith [h11]
      have h15 : a > 0 := ha1
      have h16 : (24 : ℝ) > 0 := by norm_num
      have h17 : a = (24 : ℝ) := by
        apply Real.log_injOn_pos (Set.mem_Ioi.mpr h15) (Set.mem_Ioi.mpr h16) h14
      linarith
    exact h12
  · -- Assume a = 24, prove the equation holds
    intro h
    rw [h]
    have h2 : Real.logb 2 (24 : ℝ) = Real.log (24 : ℝ) / Real.log (2 : ℝ) := by
      field_simp [Real.logb]
    have h3 : Real.logb 3 (24 : ℝ) = Real.log (24 : ℝ) / Real.log (3 : ℝ) := by
      field_simp [Real.logb]
    have h4 : Real.logb 4 (24 : ℝ) = Real.log (24 : ℝ) / Real.log (4 : ℝ) := by
      field_simp [Real.logb]
    have h5 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
      calc
        Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]
    have h6 : Real.log (24 : ℝ) = Real.log (2 : ℝ) + Real.log (3 : ℝ) + Real.log (4 : ℝ) := by
      have h7 : Real.log (24 : ℝ) = Real.log (2 * 3 * 4) := by
        norm_num
      have h8 : Real.log (2 * 3 * 4) = Real.log (2 * 3) + Real.log (4 : ℝ) := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]
      have h9 : Real.log (2 * 3) = Real.log (2 : ℝ) + Real.log (3 : ℝ) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
      linarith [h7, h8, h9]
    rw [h2, h3, h4]
    have h7 : Real.log (2 : ℝ) + Real.log (3 : ℝ) + Real.log (4 : ℝ) = Real.log (24 : ℝ) := by
      linarith [h6, h5]
    have h8 : Real.log (24 : ℝ) ≠ 0 := by
      have : (24 : ℝ) > (1 : ℝ) := by norm_num
      have : Real.log (24 : ℝ) > 0 := Real.log_pos this
      linarith
    field_simp [h8, h5]
    <;> nlinarith [h7]