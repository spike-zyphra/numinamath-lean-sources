import Mathlib

open Real

theorem inequalities_8302 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) :
  a + b + c ≥ Real.sqrt ((1 / 3) * (a + 2) * (b + 2) * (c + 2)) := by
  have h2 : (a + b + c) ^ 2 ≥ (1 / 3) * (a + 2) * (b + 2) * (c + 2) := by
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h3 : a + b + c ≥ Real.sqrt ((1 / 3) * (a + 2) * (b + 2) * (c + 2)) := by
    have h4 : Real.sqrt ((a + b + c) ^ 2) = a + b + c := by
      rw [Real.sqrt_sq]
      positivity
    have h6 : (a + b + c) ^ 2 ≥ (1 / 3) * (a + 2) * (b + 2) * (c + 2) := h2
    have h7 : Real.sqrt ((a + b + c) ^ 2) ≥ Real.sqrt ((1 / 3) * (a + 2) * (b + 2) * (c + 2)) := by
      apply Real.sqrt_le_sqrt
      linarith
    linarith [h4, h7]
  exact h3