import Mathlib

noncomputable def area: ℝ × ℝ × ℝ → ℝ := fun (a, b, c) =>
  √((a + b + c) * (b + c - a) * (a + b - c) * (a + c - b)) / 4

/-Find the area of a triangle with side lengths 14,48, and 50.-/

theorem geometry_609300 (a b c: ℝ) (ha: a = 14) (hb: b = 48) (hc: c = 50): area (a, b, c) = 336 := by

  simp [ha, hb, hc, area]
  norm_num
  field_simp
  rw [Real.sqrt_eq_iff_eq_sq]
  norm_num
  norm_num
  norm_num