import Mathlib

theorem inequalities_597775
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 ≤ 1 / (a ^ 2 + a + 1) + 1 / (b ^ 2 + b + 1) + 1 / (c ^ 2 + c + 1) := by
  have h3 : 1 / (a ^ 2 + a + 1) + 1 / (b ^ 2 + b + 1) + 1 / (c ^ 2 + c + 1) - 1 ≥ 0 := by
    have h4 : 0 < (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) := by positivity
    have h5 : 1 / (a ^ 2 + a + 1) + 1 / (b ^ 2 + b + 1) + 1 / (c ^ 2 + c + 1) - 1 =
        ( (b ^ 2 + b + 1) * (c ^ 2 + c + 1) + (a ^ 2 + a + 1) * (c ^ 2 + c + 1) + (a ^ 2 + a + 1) * (b ^ 2 + b + 1) - (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) ) / ( (a ^ 2 + a + 1) * (b ^ 2 + b + 1) * (c ^ 2 + c + 1) ) := by 
      field_simp
      <;> ring 
    rw [h5] at *
    apply div_nonneg
    · -- To prove that the numerator is ≥ 0
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc]
    · -- To prove that the denominator is ≥ 0
      positivity
  linarith