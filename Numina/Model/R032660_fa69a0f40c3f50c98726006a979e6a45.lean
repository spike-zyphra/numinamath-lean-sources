import Mathlib

theorem algebra_183552 {a b : ℝ} (ha : 0 < b) (hb : b < a)
    (h : a^2 + b^2 = 6 * a * b) : (a + b) / (a - b) = Real.sqrt 2 := by
  have h1 : 0 < a - b := by linarith
  have h2 : a > 0 := by linarith
  have h3 : ((a + b) / (a - b)) ^ 2 = 2 := by
    have h4 : a - b > 0 := by linarith
    have h7 : a * b > 0 := by nlinarith
    have h8 : ((a + b) / (a - b)) ^ 2 = ((a + b) ^ 2) / ((a - b) ^ 2) := by
      field_simp
    rw [h8]
    have h9 : (a + b) ^ 2 = 8 * (a * b) := by
      nlinarith
    have h10 : (a - b) ^ 2 = 4 * (a * b) := by
      nlinarith
    rw [h9, h10]
    field_simp
    <;> nlinarith
  have h5 : ((a + b) / (a - b)) > 0 := by
    apply div_pos
    all_goals linarith
  have h6 : (a + b) / (a - b) = Real.sqrt 2 := by
    have h7 : ((a + b) / (a - b)) ^ 2 = (Real.sqrt 2) ^ 2 := by
      rw [h3]
      all_goals
        norm_num [Real.sq_sqrt]
    have h8 : (a + b) / (a - b) ≥ 0 := by
      linarith
    have h9 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
    nlinarith [h7, Real.sqrt_nonneg 2]
  exact h6