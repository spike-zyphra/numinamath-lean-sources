import Mathlib

theorem algebra_307293 {a b : ℝ} (ha : a < 0) (hb : b < 0) (h : a < b)
    (h' : a^2 + b^2 = 4 * a * b) : (a + b) / (a - b) = Real.sqrt 3 := by

  have h1 : a - b < 0 := by linarith

  have h2 : ((a + b) / (a - b)) ^ 2 = 3 := by
    have h3 : a - b ≠ 0 := by linarith
    have h4 : ((a + b) / (a - b)) ^ 2 = ((a + b) ^ 2) / ((a - b) ^ 2) := by
      field_simp [h3]
    rw [h4]

    have h5 : (a + b : ℝ) ^ 2 = 6 * (a * b) := by
      nlinarith
    have h6 : (a - b : ℝ) ^ 2 = 2 * (a * b) := by
      nlinarith

    rw [h5, h6]
    have h7 : (6 * (a * b) ) / (2 * (a * b)) = 3 := by
      have h8 : a * b ≠ 0 := by nlinarith
      field_simp [h8]
      <;> nlinarith
    linarith

  have h3 : (a + b : ℝ) < 0 := by linarith
  have h4 : (a + b) / (a - b) ≥ 0 := by
    apply div_nonneg_of_nonpos
    linarith
    linarith

  have h5 : (a + b) / (a - b) = Real.sqrt 3 := by
    have h6 : ((a + b) / (a - b)) ^ 2 = 3 := h2
    have h7 : (a + b) / (a - b) ≥ 0 := h4
    have h8 : Real.sqrt 3 ≥ 0 := by positivity

    have h9 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [sq_nonneg ((a + b) / (a - b) - Real.sqrt 3)]

  exact h5