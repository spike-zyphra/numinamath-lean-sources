import Mathlib

theorem inequalities_129015 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b ≥ 1) :
    (a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) ≥ 16 := by
  have h1 : 0 < a + 1 := by linarith
  have h2 : 0 < b + 1 := by linarith
  have h3 : 0 < (a + 1) * (b + 1) := mul_pos h1 h2
  have eq1 : (a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) - 16 =
      ((a ^ 2 + a + 2 * a * b + 2 * b + 2) * (b ^ 2 + b + 2 * a * b + 2 * a + 2) - 16 * ((a + 1) * (b + 1))) / ((a + 1) * (b + 1)) := by
    field_simp
    <;> ring

  have eq4 : ((a ^ 2 + a + 2 * a * b + 2 * b + 2) * (b ^ 2 + b + 2 * a * b + 2 * a + 2) - 16 * ((a + 1) * (b + 1)) ) ≥ 0 := by 
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1),
      mul_pos ha hb, hab,
      sq_nonneg (a * b), mul_pos ha (show 0 < b by linarith),
      sq_nonneg (a * a - b * b), sq_nonneg (a + b - 2)]

  have h4 : (a + 2 * b + 2 / (a + 1)) * (b + 2 * a + 2 / (b + 1)) - 16 ≥ 0 := by 
    rw [eq1]
    apply div_nonneg
    linarith [eq4]
    positivity
  linarith