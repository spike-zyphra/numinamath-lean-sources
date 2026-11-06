import Mathlib



theorem inequalities_80941 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a * b = 1) :
    1 / (a ^ 3 + 3 * b) + 1 / (b ^ 3 + 3 * a) ≤ 1 / 2 := by

  have h1 : 0 < a ^ 3 + 3 * b := by positivity
  have h2 : 0 < b ^ 3 + 3 * a := by positivity

  suffices (1 / (a ^ 3 + 3 * b) + 1 / (b ^ 3 + 3 * a) - 1 / 2 ≤ 0) by linarith

  have h_ineq : 1 / (a ^ 3 + 3 * b) + 1 / (b ^ 3 + 3 * a) - 1 / 2 = 
      (2 * (b ^ 3 + 3 * a) + 2 * (a ^ 3 + 3 * b) - (a ^ 3 + 3 * b) * (b ^ 3 + 3 * a)) / (2 * (a ^ 3 + 3 * b) * (b ^ 3 + 3 * a)) := by
    field_simp
    ring

  rw [h_ineq]

  apply div_nonpos_of_nonpos_of_nonneg
  · -- Show that the numerator is ≤ 0
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1), sq_nonneg (b - 1), 
        sq_nonneg (a * b - 1), sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), 
        sq_nonneg (a * b - 1), sq_nonneg (a * b + 1 - 2), 
        hab, mul_pos ha hb,
        sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b - 1)
        ]
  · -- Show that the denominator is ≥ 0
    positivity