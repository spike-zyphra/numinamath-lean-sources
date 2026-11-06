import Mathlib

theorem algebra_3226 (x : ℝ) (hx : x ≠ (292 / 36) ∧ x ≠ (-2)) (h : (7 * x + 17) / (x + 2) = (252 * x - 2020) / (36 * x - 292)) : x = 11 := by
  have hx1 : x + 2 ≠ 0 := by
    intro h1
    apply hx.right
    linarith
  have hx2 : 36 * x - 292 ≠ 0 := by
    intro h2
    apply hx.left
    linarith
  field_simp [(show x + 2 ≠ 0 by assumption), (show 36 * x - 292 ≠ 0 by assumption)] at h
  linarith