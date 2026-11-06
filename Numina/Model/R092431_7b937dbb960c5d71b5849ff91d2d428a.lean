import Mathlib

open Real Set

theorem inequalities_296873 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a^3 + b^3 + 4) / ((a + 1) * (b + 1)) ≥ 3 / 2 := by
  have h1 : 0 < (a + 1) * (b + 1) := by
    apply mul_pos
    linarith
    linarith
  have h2 : 2 * (a ^ 3 + b ^ 3 + 4) - 3 * ((a + 1) * (b + 1)) ≥ 0 := by 
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b),
      sq_nonneg (a + 1), sq_nonneg (b + 1),
      sq_nonneg (a + 1 - (b + 1)), sq_nonneg (a^2 - b^2), sq_nonneg (a * b - 1),
      mul_pos ha hb, mul_pos ha (show 0 < b + 1 by linarith), mul_pos hb (show 0 < a + 1 by linarith)]
  have h3 : 2 * (a ^ 3 + b ^ 3 + 4) ≥ 3 * ((a + 1) * (b + 1)) := by linarith
  have h4 : (a^3 + b^3 + 4) / ((a + 1) * (b + 1)) - 3 / 2 ≥ 0 := by
    have h5 : (a^3 + b^3 + 4) / ((a + 1) * (b + 1)) - 3 / 2 =
        (2 * (a^3 + b^3 + 4) - 3 * ((a + 1) * (b + 1))) / (2 * ((a + 1) * (b + 1))) := by
      field_simp
      <;> ring 
    rw [h5]
    apply div_nonneg 
    linarith 
    positivity 
  linarith