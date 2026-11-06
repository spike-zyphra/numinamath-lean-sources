import Mathlib

theorem inequalities_596863 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a^2 / b + b^2 / a ≥ a + b := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : a^2 / b + b^2 / a - (a + b) ≥ 0 := by
    have h3 : a^2 / b + b^2 / a - (a + b) = (a^3 + b^3 - (a^2 * b + a * b^2)) / (a * b) := by
      field_simp [hb.ne.symm, ha.ne.symm]
      ring
    rw [h3]
    have h4 : a^3 + b^3 - (a^2 * b + a * b^2) = (a - b) ^ 2 * (a + b) := by
      ring
    have h5 : (a - b) ^ 2 * (a + b) ≥ 0 := by
      have h6 : (a - b) ^ 2 ≥ 0 := by
        apply sq_nonneg
      have h7 : a + b > 0 := add_pos ha hb
      nlinarith
    have h8 : (a^3 + b^3 - (a^2 * b + a * b^2)) ≥ 0 := by
      linarith [h4, h5]
    apply div_nonneg
    linarith
    all_goals nlinarith
  linarith