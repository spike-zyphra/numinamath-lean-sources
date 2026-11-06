import Mathlib

theorem algebra_203546 {a : ℝ} (ha : 1 < a) (h : Real.logb 5 a + Real.logb 3 a = Real.logb 5 a * Real.logb 3 a) :
    a = 15 := by
  have h1 : Real.logb 5 a = Real.log a / Real.log (5 : ℝ) := by
    field_simp [Real.logb]
  have h2 : Real.logb 3 a = Real.log a / Real.log (3 : ℝ) := by
    field_simp [Real.logb]
  rw [h1, h2] at h
  have h3 : Real.log a ≠ 0 := by
    have ha' : 1 < a := ha
    have h4 : Real.log a > 0 := by
      apply Real.log_pos
      linarith
    linarith
  have h4 : Real.log (5 : ℝ) > 0 := by
    have h5 : (5 : ℝ) > 1 := by norm_num
    have h6 : Real.log (5 : ℝ) > 0 := by
      apply Real.log_pos
      all_goals linarith
    linarith
  have h5 : Real.log (3 : ℝ) > 0 := by
    have h6 : (3 : ℝ) > 1 := by norm_num
    have h7 : Real.log (3 : ℝ) > 0 := by
      apply Real.log_pos
      all_goals linarith
    linarith
  have eq1 : Real.log a * Real.log (3 : ℝ) + Real.log a * Real.log (5 : ℝ) = (Real.log a) ^ 2 := by
    field_simp [h4, h5] at h ⊢
    nlinarith
  have eq2 : Real.log a * (Real.log a - (Real.log (3 : ℝ) + Real.log (5 : ℝ))) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp eq2) with h6 h7
  · -- h6 : Real.log a = 0
    exfalso
    have h7 : Real.log a > 0 := by
      apply Real.log_pos
      linarith
    linarith
  · -- h7 : Real.log a - (Real.log (3 : ℝ) + Real.log (5 : ℝ)) = 0
    have h8 : Real.log a = Real.log (3 : ℝ) + Real.log (5 : ℝ) := by linarith
    have h9 : Real.log (3 * (5 : ℝ)) = Real.log (3 : ℝ) + Real.log (5 : ℝ) := by
      have h91 : Real.log (3 * (5 : ℝ)) = Real.log (3 : ℝ) + Real.log (5 : ℝ) := by
        rw [Real.log_mul (by norm_num) (by norm_num)]
      linarith [h91]
    have h10 : Real.log a = Real.log (15 : ℝ) := by
      have h11 : Real.log (15 : ℝ) = Real.log (3 * (5 : ℝ)) := by
        norm_num
      have h12 : Real.log (3 * (5 : ℝ)) = Real.log (3 : ℝ) + Real.log (5 : ℝ) := h9
      linarith [h8, h11, h12]
    have h12 : a = (15 : ℝ) := by
      have h13 : a > 0 := by linarith
      have h14 : (15 : ℝ) > 0 := by norm_num
      have h15 : Real.log a = Real.log (15 : ℝ) := h10
      have h16 : a = (15 : ℝ) := by
        apply Real.log_injOn_pos (Set.mem_Ioi.mpr h13) (Set.mem_Ioi.mpr h14) h15
      linarith
    linarith