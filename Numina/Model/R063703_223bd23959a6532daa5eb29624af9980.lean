import Mathlib

theorem algebra_8115 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    (1 - a / 100) * (1 - b / 100) < (1 - (a + b) / 2 / 100) ^ 2 := by
  have h1 : (1 - (a + b) / 2 / 100 : ℝ) ^ 2 - (1 - a / 100) * (1 - b / 100) > 0 := by
    have h2 : (a - b) ^ 2 > 0 := by
      apply sq_pos_of_ne_zero
      intro h
      apply hab
      linarith
    have h3 : (1 - (a + b) / 2 / 100 : ℝ) ^ 2 - (1 - a / 100) * (1 - b / 100) = (a - b)^2 / 40000 := by
      ring_nf
    rw [h3]
    have h4 : (a - b)^2 / 40000 > 0 := by
      apply div_pos
      exact h2
      norm_num
    linarith
  linarith [h1]