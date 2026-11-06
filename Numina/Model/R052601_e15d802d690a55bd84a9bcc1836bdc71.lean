import Mathlib

theorem inequalities_110699 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    1 / a + 1 / b ≥ 4 / (a + b) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < a + b := add_pos ha hb

  have h3 : (a + b) ^ 2 ≥ 4 * a * b := by
    nlinarith [sq_nonneg (a - b)]

  have h4 : (1 / a + 1 / b) - (4 / (a + b)) ≥ 0 := by
    have h5 : (1 / a + 1 / b) - (4 / (a + b)) = ((a + b) ^ 2 - 4 * a * b) / (a * b * (a + b)) := by
      field_simp [ha.ne.symm, hb.ne.symm, show a + b ≠ 0 by linarith]
      ring
    rw [h5]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b)]
    positivity

  linarith