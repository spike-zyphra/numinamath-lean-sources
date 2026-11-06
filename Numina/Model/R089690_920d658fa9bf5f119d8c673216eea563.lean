import Mathlib

theorem algebra_1672 (m a : ℝ) (ha : 0 < a) (hm : 0 < m) (v : ℝ)
    (h : v = 2 * m / (m / (3 * a) + m / (2 * a))) : v = 12 / 5 * a := by
  rw [h]
  have h1 : m / (3 * a) + m / (2 * a) = 5 * m / (6 * a) := by
    field_simp
    ring
  rw [h1]
  field_simp
  <;> ring