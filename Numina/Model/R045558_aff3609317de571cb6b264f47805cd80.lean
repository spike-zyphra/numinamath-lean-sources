import Mathlib

theorem inequalities_290177 (a b : ℝ) (ha : 0 < b) (hb : b < a) :
    Real.sqrt (a / b) > (3 * a + b) / (a + 3 * b) := by
  have h1 : 0 < a := by linarith
  have h2 : 0 < b := by linarith
  have h3 : 0 < a / b := by
    apply div_pos
    linarith
    linarith
  have h4 : Real.sqrt (a / b) ≥ 0 := by positivity
  have h5 : (Real.sqrt (a / b)) ^ 2 = a / b := Real.sq_sqrt (by positivity)
  have h6 : a / b > ((3 * a + b) / (a + 3 * b)) ^ 2 := by
    have h7 : 0 < a := by linarith
    have h8 : 0 < b := by linarith
    have h9 : 0 < a + 3 * b := by linarith
    have h10 : a / b - ((3 * a + b) / (a + 3 * b)) ^ 2 > 0 := by
      have h11 : a / b - ((3 * a + b) / (a + 3 * b)) ^ 2 =
          (a * (a + 3 * b) ^ 2 - b * (3 * a + b) ^ 2) / (b * (a + 3 * b) ^ 2) := by
        field_simp
        <;> ring
      rw [h11]
      have h12 : a * (a + 3 * b) ^ 2 - b * (3 * a + b) ^ 2 > 0 := by
        nlinarith [sq_pos_of_pos (show (0 : ℝ) < a - b by linarith), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a * b), sq_pos_of_pos (show (0 : ℝ) < a by linarith), sq_pos_of_pos (show (0 : ℝ) < b by linarith)]
      have h13 : b * (a + 3 * b) ^ 2 > 0 := by
        positivity
      apply div_pos
      linarith
      linarith
    nlinarith
  have h7 : Real.sqrt (a / b) > (3 * a + b) / (a + 3 * b) := by
    have h8 : Real.sqrt (a / b) > Real.sqrt (((3 * a + b) / (a + 3 * b)) ^ 2) := by
      apply Real.sqrt_lt_sqrt
      · -- Show $0 \leq (3a + b)/(a + 3b)^2$
        positivity
      all_goals -- Show $a/b > (3a + b)/(a + 3b)^2$
        nlinarith [h6]
    have h9 : Real.sqrt (((3 * a + b) / (a + 3 * b)) ^ 2) = (3 * a + b) / (a + 3 * b) := by
      rw [Real.sqrt_sq (by positivity)]
    nlinarith [h8, h9]
  exact h7