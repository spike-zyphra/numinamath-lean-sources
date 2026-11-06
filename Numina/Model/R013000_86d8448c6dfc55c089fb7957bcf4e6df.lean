import Mathlib

theorem inequalities_291952 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    12 ≤ a^2 / (b - 1) + b^2 / (c - 1) + c^2 / (a - 1) := by
  have h1 : 0 < b - 1 := by linarith
  have h2 : 0 < c - 1 := by linarith
  have h3 : 0 < a - 1 := by linarith
  have h4 : a^2 / (b - 1) + 4 * (b - 1) ≥ 4 * a := by
    have h5 : a^2 / (b - 1) + 4 * (b - 1) - 4 * a ≥ 0 := by
      have h6 : (a^2 / (b - 1) + 4 * (b - 1) - 4 * a) = (a^2 + 4 * (b - 1)^2 - 4 * a * (b - 1)) / (b - 1) := by
        field_simp
        <;> ring
      rw [h6]
      apply div_nonneg
      nlinarith [sq_nonneg (a - 2 * (b - 1)), sq_nonneg (a - 3)]
      linarith
    linarith
  have h5 : b^2 / (c - 1) + 4 * (c - 1) ≥ 4 * b := by
    have h6 : b^2 / (c - 1) + 4 * (c - 1) - 4 * b ≥ 0 := by
      have h7 : (b^2 / (c - 1) + 4 * (c - 1) - 4 * b) = (b^2 + 4 * (c - 1)^2 - 4 * b * (c - 1)) / (c - 1) := by
        field_simp
        <;> ring
      rw [h7]
      apply div_nonneg
      nlinarith [sq_nonneg (b - 2 * (c - 1)), sq_nonneg (b - 3)]
      linarith
    linarith
  have h6 : c^2 / (a - 1) + 4 * (a - 1) ≥ 4 * c := by
    have h7 : c^2 / (a - 1) + 4 * (a - 1) - 4 * c ≥ 0 := by
      have h8 : (c^2 / (a - 1) + 4 * (a - 1) - 4 * c) = (c^2 + 4 * (a - 1)^2 - 4 * c * (a - 1)) / (a - 1) := by
        field_simp
        <;> ring
      rw [h8]
      apply div_nonneg
      nlinarith [sq_nonneg (c - 2 * (a - 1)), sq_nonneg (c - 3)]
      linarith
    linarith
  have h7 : a^2 / (b - 1) + b^2 / (c - 1) + c^2 / (a - 1) + 4 * (a + b + c - 3) ≥ 4 * (a + b + c) := by
    linarith [h4, h5, h6]
  linarith