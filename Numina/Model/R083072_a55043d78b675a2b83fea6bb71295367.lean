import Mathlib

theorem inequalities_156677 (a : ℝ) (ha : a > 0) :
    ((a^3 + 1) / (a^2 + 1))^2 ≥ a^2 - a + 1 := by
  have h1 : (a ^ 2 + 1) ^ 2 > 0 := by
    positivity
  have h2 : (a ^ 3 + 1) ^ 2 - (a ^ 2 - a + 1) * (a ^ 2 + 1) ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a ^ 2 - a + 1), sq_nonneg (a), sq_nonneg (a - 1), sq_nonneg (a * (a - 1)), sq_nonneg (a * (a ^ 2 - a + 1))]
  have h3 : ((a^3 + 1) / (a^2 + 1))^2 - (a^2 - a + 1) ≥ 0 := by
    have h4 : ((a^3 + 1) / (a^2 + 1))^2 - (a^2 - a + 1) =
      ((a ^ 3 + 1) ^ 2 - (a ^ 2 - a + 1) * (a ^ 2 + 1) ^ 2) / ( (a ^ 2 + 1) ^ 2 ) := by
      field_simp
      <;> ring
    rw [h4]
    apply div_nonneg
    linarith
    positivity
  linarith