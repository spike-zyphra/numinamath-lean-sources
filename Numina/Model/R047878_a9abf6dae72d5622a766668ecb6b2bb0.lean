import Mathlib

theorem inequalities_135690 (x y z : ℝ) (h : x^4 + y^4 + z^4 + x * y * z = 4) :
    x ≤ 2 ∧ Real.sqrt (2 - x) ≥ (y + z) / 2 := by
  have h1 : x ≤ 2 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y ^ 2 - 1), sq_nonneg (z ^ 2 - 1),
      sq_nonneg (y - z), sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - z ^ 2),
      sq_nonneg (y + z), sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  have h2 : Real.sqrt (2 - x) ≥ (y + z) / 2 := by
    have h3 : (2 - x) ≥ 0 := by linarith
    have h4 : ( (y + z) / 2 ) ^ 2 ≤ 2 - x := by
      nlinarith [sq_nonneg (y - z), sq_nonneg (y + z - 2), sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (y ^ 2 - 1), sq_nonneg (z ^ 2 - 1), sq_nonneg (x + 1), sq_nonneg (y - 1), sq_nonneg (z - 1), h1, sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (y * z - 1)]
    have h5 : ( (y + z ) / 2 ) ^ 2 ≤ (2 - x) := h4
    have h6 : Real.sqrt ((2 - x)) ≥ Real.sqrt ((( (y + z ) / 2 ) ^ 2)) := Real.sqrt_le_sqrt (show ( (y + z ) / 2 ) ^ 2 ≤ (2 - x) by linarith )
    have h7 : Real.sqrt ((( (y + z ) / 2 ) ^ 2)) = |( (y + z ) / 2 )| := by
      rw [Real.sqrt_sq_eq_abs]
    have h8 : |( (y + z ) / 2 )| ≥ ( (y + z ) / 2 ) := by
      cases abs_cases ( (y + z ) / 2 ) with
      | inl h1 =>
        linarith
      | inr h2 =>
        linarith
    linarith [Real.sqrt_nonneg (2 - x), Real.sqrt_nonneg ((( (y + z ) / 2 ) ^ 2)), h7, h8, h6]
  constructor
  · linarith
  · exact h2