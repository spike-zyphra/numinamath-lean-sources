import Mathlib

theorem inequalities_102950 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 3) :
    a / (1 + b) + b / (1 + c) + c / (1 + a) ≥
    1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) := by
  have h1 : a / (1 + b) + b / (1 + c) + c / (1 + a) - (1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c)) ≥ 0 := by
    have h2 : a / (1 + b) + b / (1 + c) + c / (1 + a) - (1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c)) = (a - 1) / (1 + b) + (b - 1) / (1 + c) + (c - 1) / (1 + a) := by 
      field_simp
      <;> ring
    rw [h2]
    have h3 : (a - 1) / (1 + b) + (b - 1) / (1 + c) + (c - 1) / (1 + a) ≥ 0 := by
      have h4 : 0 < (1 + a) * (1 + b) * (1 + c) := by
        positivity
      have h5 : (a - 1) / (1 + b) + (b - 1) / (1 + c) + (c - 1) / (1 + a) = ((a - 1) * (1 + a) * (1 + c) + (b - 1) * (1 + b) * (1 + a) + (c - 1) * (1 + c) * (1 + b)) / ((1 + a) * (1 + b) * (1 + c)) := by
        field_simp
        <;> ring
      rw [h5] at *
      apply div_nonneg
      · -- Prove the numerator is non-negative
        have h7 : a + b + c = 3 := h
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
      · -- Prove the denominator is non-negative
        positivity
    linarith
  linarith