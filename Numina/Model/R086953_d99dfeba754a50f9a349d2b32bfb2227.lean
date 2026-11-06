import Mathlib

theorem algebra_93042 (x : ℝ) (hx : x > 0 ∧ x ≠ 1) :
    1 / Real.logb 3 x + 1 / Real.logb 4 x + 1 / Real.logb 5 x = 1 / Real.logb 60 x := by
  rcases hx with ⟨hx_pos, hx_ne_1⟩
  have h1 : Real.logb 3 x = Real.log x / Real.log 3 := by
    field_simp [Real.logb]
    all_goals linarith
  have h2 : Real.logb 4 x = Real.log x / Real.log 4 := by
    field_simp [Real.logb]
    all_goals linarith
  have h3 : Real.logb 5 x = Real.log x / Real.log 5 := by
    field_simp [Real.logb]
    all_goals linarith
  have h4 : Real.logb 60 x = Real.log x / Real.log 60 := by
    field_simp [Real.logb]
    all_goals linarith
  have h5 : 1 / Real.logb 3 x = Real.log 3 / Real.log x := by
    rw [h1]
    field_simp [(show Real.log x ≠ 0 by
      have h1' : x > 0 := hx_pos
      have h2' : x ≠ 1 := hx_ne_1
      have : Real.log x ≠ 0 := by
        exact Real.log_ne_zero_of_pos_of_ne_one h1' h2'
      exact this)]
    all_goals linarith
  have h6 : 1 / Real.logb 4 x = Real.log 4 / Real.log x := by
    rw [h2]
    field_simp [(show Real.log x ≠ 0 by
      have h1' : x > 0 := hx_pos
      have h2' : x ≠ 1 := hx_ne_1
      have : Real.log x ≠ 0 := by
        exact Real.log_ne_zero_of_pos_of_ne_one h1' h2'
      exact this)]
    all_goals linarith
  have h7 : 1 / Real.logb 5 x = Real.log 5 / Real.log x := by
    rw [h3]
    field_simp [(show Real.log x ≠ 0 by
      have h1' : x > 0 := hx_pos
      have h2' : x ≠ 1 := hx_ne_1
      have : Real.log x ≠ 0 := by
        exact Real.log_ne_zero_of_pos_of_ne_one h1' h2'
      exact this)]
    all_goals linarith
  have h8 : 1 / Real.logb 60 x = Real.log 60 / Real.log x := by
    rw [h4]
    field_simp [(show Real.log x ≠ 0 by
      have h1' : x > 0 := hx_pos
      have h2' : x ≠ 1 := hx_ne_1
      have : Real.log x ≠ 0 := by
        exact Real.log_ne_zero_of_pos_of_ne_one h1' h2'
      exact this)]
    all_goals linarith
  have h9 : Real.log 60 = Real.log 3 + Real.log 4 + Real.log 5 := by
    have h10 : Real.log 60 = Real.log (3 * 4 * 5) := by norm_num
    rw [h10]
    have h11 : Real.log (3 * 4 * 5) = Real.log (3 * 4) + Real.log 5 := by
      have h12 : (3 * 4 * 5 : ℝ) = (3 * 4) * 5 := by ring
      rw [h12]
      have h13 : (3 * 4 : ℝ) > 0 := by norm_num
      have h14 : (5 : ℝ) > 0 := by norm_num
      rw [Real.log_mul (by linarith) (by linarith)]
    have h16 : Real.log (3 * 4) = Real.log 3 + Real.log 4 := by
      have h17 : (3 : ℝ) > 0 := by norm_num
      have h18 : (4 : ℝ) > 0 := by norm_num
      rw [Real.log_mul (by linarith) (by linarith)]
    linarith [h11, h16]
  rw [h5, h6, h7, h8]
  rw [h9]
  have hx' : Real.log x ≠ 0 := by
    have h1' : x > 0 := hx_pos
    have h2' : x ≠ 1 := hx_ne_1
    have : Real.log x ≠ 0 := by
      exact Real.log_ne_zero_of_pos_of_ne_one h1' h2'
    exact this
  field_simp [hx']
  <;> ring_nf <;> field_simp [hx'] at *
  <;> nlinarith