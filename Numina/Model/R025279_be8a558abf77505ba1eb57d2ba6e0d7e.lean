import Mathlib

theorem algebra_318719 (v1 v2 v3 : ℝ) (h : v1 > 0 ∧ v2 > 0 ∧ v3 > 0)
    (t1 t2 : ℝ) (ht1 : t1 = 1 / 3 * (d / v1 + d / v2 + d / v3))
    (ht2 : t2 = d / (3 * v1) + d / (3 * v2) + d / (3 * v3)) :
    t1 ≤ t2 := by
  have h1 : v1 > 0 := h.1
  have h2 : v2 > 0 := h.2.1
  have h3 : v3 > 0 := h.2.2
  have h4 : t1 = t2 := by
    rw [ht1, ht2]
    field_simp
    <;> ring
  linarith [h4]