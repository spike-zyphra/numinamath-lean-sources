import Mathlib

theorem algebra_214565 (a : ℝ) (ha : a > 0) (p q : ℝ)
    (x : ℝ) (hx : x^2 + p * x + q = 0) :
    x ≥ (4 * q - (p + a)^2) / (4 * a) := by

  have h1 : 4 * a > 0 := by linarith
  have h2 : 4 * a * x ≥ 4 * q - (p + a)^2 := by
    have hq : q = -x^2 - p * x := by linarith [hx]
    rw [hq]
    nlinarith [sq_nonneg (2 * x + p + a)]
  have h3 : x - (4 * q - (p + a)^2) / (4 * a) ≥ 0 := by
    have h4 : (x - (4 * q - (p + a)^2) / (4 * a)) = (4 * a * x - (4 * q - (p + a)^2)) / (4 * a) := by
      field_simp
      <;> ring
    rw [h4]
    apply div_nonneg
    linarith [h2]
    all_goals linarith [show 0 < 4 * a by linarith]
  linarith [h3]