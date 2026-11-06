import Mathlib

theorem inequalities_597910 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) ≤ 1 := by
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) - 1 ≤ 0 := by
    have h3 : a * b * c = 1 := habc
    have pos1 : 0 < (a + b + 1) * (b + c + 1) * (c + a + 1) := by positivity
    have h4 : 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1) - 1 =
        ( (b + c + 1) * (c + a + 1) + (a + b + 1) * (c + a + 1) + (a + b + 1) * (b + c + 1) - (a + b + 1) * (b + c + 1) * (c + a + 1) ) / ( (a + b + 1) * (b + c + 1) * (c + a + 1) ) := by
      field_simp
      <;> ring
    rw [h4] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is ≤ 0
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1), 
                  sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc]
    · -- Show that the denominator is ≥ 0
      positivity
  linarith