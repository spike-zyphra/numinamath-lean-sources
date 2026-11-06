import Mathlib
open Real

theorem algebra_319 {a b : ℝ} (ha : a < b) (hb : b < 0) (h : a^2 + b^2 = 4 * a * b) :
    (a + b) / (a - b) = sqrt 3 := by
  have h1 : a - b < 0 := by linarith
  have h4 : ((a + b) / (a - b)) ^2 = 3 := by
    have h5 : (a - b) < 0 := by linarith
    have h6 : (a + b) ^2 = 6 * (a * b) := by
      nlinarith [h]
    have h7 : (a - b) ^2 = 2 * (a * b) := by
      nlinarith [h]
    have h8 : (a * b) > 0 := by
      nlinarith [show a < 0 by nlinarith, show b < 0 by linarith, show a < b by linarith]
    have h9 : ((a + b) / (a - b)) ^2 = ((a + b) ^2) / ((a - b) ^2) := by
      field_simp [show a - b ≠ 0 by linarith]
    rw [h9]
    rw [h6, h7]
    field_simp [h8]
    <;> nlinarith
  have h3 : (a + b) / (a - b) > 0 := by
    apply div_pos_of_neg_of_neg
    · -- Show a + b < 0.
      nlinarith
    · -- Show a - b < 0
      linarith
  have h9 : ( (a + b) / (a - b) ) = Real.sqrt 3 := by
    have h10 : ( (a + b) / (a - b) ) ≥ 0 := by linarith
    have h11 : (Real.sqrt 3) ^2 = 3 := Real.sq_sqrt (by linarith)
    have h12 : ((a + b) / (a - b)) ^2 = (Real.sqrt 3) ^2 := by
      rw [h4, h11]
    have h14 : ( (a + b) / (a - b) ) = (Real.sqrt 3) := by
      nlinarith [Real.sqrt_nonneg 3]
    exact h14
  exact h9