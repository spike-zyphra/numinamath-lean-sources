import Mathlib

theorem algebra_191560 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a^2 + b^2 = 8 * a * b) :
    |(a + b) / (a - b)| = Real.sqrt 15 / 3 := by

  have h1 : |(a + b) / (a - b)| = Real.sqrt ((a + b) ^ 2 / (a - b) ^ 2) := by
    have h9 : (a - b) ≠ 0 := by
      by_contra h10
      have eq1 : a - b = 0 := by linarith
      have eq2 : a = b := by linarith [eq1]
      have eq3 : a^2 + b^2 = 8 * a * b := h
      rw [show b = a by linarith [eq2]] at eq3
      have eq4 : 2 * a^2 = 8 * a^2 := by
        linarith
      have eq5 : 6 * a^2 = 0 := by linarith
      have eq6 : a^2 = 0 := by linarith
      have eq7 : a = 0 := by
        nlinarith
      contradiction
    have h2 : ((a + b) / (a - b)) ^ 2 = (a + b) ^ 2 / (a - b) ^ 2 := by
      field_simp [h9]
      <;> nlinarith
    rw [← h2]
    have h3 : |(a + b) / (a - b)| = Real.sqrt (((a + b) / (a - b)) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h3]
  have h2 : (a + b) ^ 2 = 10 * (a * b) := by
    nlinarith
  have h3 : (a - b) ^ 2 = 6 * (a * b) := by
    nlinarith
  have h4 : (a * b) ≠ 0 := by
    apply mul_ne_zero
    exact ha
    exact hb
  have h5 : (a + b) ^ 2 / (a - b) ^ 2 = (5 / 3) := by
    rw [h2, h3]
    have h6 : (a * b) ≠ 0 := h4
    field_simp [h6]
    <;> nlinarith
  have h6 : Real.sqrt ((a + b) ^ 2 / (a - b) ^ 2) = Real.sqrt (5 / 3) := by
    rw [h5]
  have h7 : Real.sqrt (5 / 3) = Real.sqrt 15 / 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h1, h6, h7]
  all_goals
    have h9 : (a - b) ≠ 0 := by
      by_contra h10
      have eq1 : a - b = 0 := by linarith
      have eq2 : a = b := by linarith [eq1]
      have eq3 : a^2 + b^2 = 8 * a * b := h
      rw [show b = a by linarith [eq2]] at eq3
      have eq4 : 2 * a^2 = 8 * a^2 := by
        linarith
      have eq5 : 6 * a^2 = 0 := by linarith
      have eq6 : a^2 = 0 := by linarith
      have eq7 : a = 0 := by
        nlinarith
      contradiction
    all_goals nlinarith