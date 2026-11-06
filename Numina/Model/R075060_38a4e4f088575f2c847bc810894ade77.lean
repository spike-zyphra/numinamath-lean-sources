import Mathlib

theorem inequalities_276983 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a / b = b / c) : a^2 + c^2 ≥ 2 * b^2 := by
  have h1 : a * c = b ^ 2 := by
    field_simp [hb, hc] at h
    nlinarith
  have h2 : a^2 + c^2 ≥ 2 * (a * c) := by
    linarith [sq_nonneg (a - c)]
  rw [h1] at h2
  linarith