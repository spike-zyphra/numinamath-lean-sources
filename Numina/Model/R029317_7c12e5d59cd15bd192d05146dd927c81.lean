import Mathlib

theorem inequalities_598658 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) ≥ 1 / 2 := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith
  have h5 : a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) ≥ 1 / 2 := by
    have pos1 : 0 < (b + c) * (c + a) * (a + b) := by positivity
    have : a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) - 1 / 2 ≥ 0 := by
      have : a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) - 1 / 2 =
          (a^2 * (c + a) * (a + b) + b^2 * (b + c) * (a + b) + c^2 * (b + c) * (c + a) - (1 / 2) * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
        field_simp
        <;> ring
      rw [this] at *
      apply div_nonneg
      -- Show the numerator is non-negative
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                  mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
                  mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ c by linarith), 
                  mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith)]
      -- Show the denominator is positive
      positivity
    linarith
  linarith [h5]