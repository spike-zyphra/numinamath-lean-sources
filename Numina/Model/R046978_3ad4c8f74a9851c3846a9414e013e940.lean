import Mathlib

theorem algebra_328243 (a : ℝ) (ha : -1 < a ∧ a < 0) :
    Real.sqrt ((a + 1 / a) ^ 2 - 4) + Real.sqrt ((a - 1 / a) ^ 2 + 4) = -2 / a := by
  have h1 : -1 < a := ha.1
  have h2 : a < 0 := ha.2
  have h3 : (a + 1 / a) ^ 2 - 4 = (a - 1 / a) ^ 2 := by
    field_simp [(show a ≠ 0 by linarith)]
    <;> nlinarith
  have h4 : Real.sqrt ((a + 1 / a) ^ 2 - 4) = |a - 1 / a| := by
    rw [h3]
    have h5 : Real.sqrt ((a - 1 / a) ^ 2) = |a - 1 / a| := by
      rw [Real.sqrt_sq_eq_abs]
    exact h5
  have h6 : (a - 1 / a) ^ 2 + 4 = (a + 1 / a) ^ 2 := by 
    field_simp [(show a ≠ 0 by linarith)]
    <;> nlinarith
  have h7 : Real.sqrt ((a - 1 / a) ^ 2 + 4) = |a + 1 / a| := by
    rw [h6]
    have h8 : Real.sqrt ((a + 1 / a) ^ 2) = |a + 1 / a| := by
      rw [Real.sqrt_sq_eq_abs]
    exact h8
  have h8 : a - 1 / a > 0 := by
    have ha5 : 1 / a < a := by
      have ha6 : a * (1 / a) = 1 := by
        field_simp [(show a ≠ 0 by linarith)]
      nlinarith [sq_nonneg (a + 1), sq_pos_of_pos (show (0 : ℝ) < 1 by norm_num), 
        h1, h2, show a ^ 2 < 1 by nlinarith [h1, h2]
      ]
    linarith
  have h9 : |a - 1 / a| = a - 1 / a := by
    rw [abs_of_pos h8]
  have h11 : a + 1 / a < 0 := by
    have ha6 : 1 / a < 0 := by
      apply div_neg_of_pos_of_neg
      norm_num
      linarith
    linarith
  have h10 : |a + 1 / a| = -(a + 1 / a) := by
    rw [abs_of_neg h11]
  rw [h4, h7, h9, h10]
  field_simp [(show a ≠ 0 by linarith)]
  <;> nlinarith