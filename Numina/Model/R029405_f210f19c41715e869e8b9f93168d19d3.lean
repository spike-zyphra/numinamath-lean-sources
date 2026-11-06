import Mathlib

theorem inequalities_599089 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a * b = 1) :
    b / (1 + a ^ 4) + a / (1 + b ^ 4) ≥ 1 := by
  have h1 : b = 1 / a := by
    have hne : a ≠ 0 := by linarith
    field_simp [hne]
    nlinarith
  have eq1 : a / (1 + b ^ 4) = a ^ 5 / (1 + a ^ 4) := by
    rw [show b = 1 / a by linarith [h1]]
    field_simp [(show a ≠ 0 by linarith)]
    <;> nlinarith [sq_pos_of_pos ha]
  have eq2 : b / (1 + a ^ 4) = 1 / (a * (1 + a ^ 4)) := by
    rw [show b = 1 / a by linarith [h1]]
    field_simp [(show a ≠ 0 by linarith)]
    <;> nlinarith [sq_pos_of_pos ha]
  rw [eq1, eq2]
  have h4 : 1 / (a * (1 + a ^ 4)) + a ^ 5 / (1 + a ^ 4) ≥ 1 := by
    have h5 : 0 < a * (1 + a ^ 4) := by
      apply mul_pos
      linarith
      nlinarith [sq_nonneg (a ^ 2)]
    have h6' : 1 / (a * (1 + a ^ 4)) + a ^ 5 / (1 + a ^ 4) - 1 ≥ 0 := by
      have h8' : (1 / (a * (1 + a ^ 4)) + a ^ 5 / (1 + a ^ 4) ) - 1 = ( (1 + a^6 ) - a * (1 + a ^ 4) ) / (a * (1 + a^4)) := by
        field_simp [(show a ≠ 0 by linarith), (show 1 + a^4 ≠ 0 by nlinarith)]
        ring
      rw [h8']
      have h9 : (1 + a^6 ) - a * (1 + a^4) ≥ 0 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (a ^ 2 - 1), sq_nonneg (a ^ 2), sq_nonneg (a ^ 4 - 1)]
      apply div_nonneg
      linarith
      all_goals nlinarith
    linarith
  linarith