import Mathlib

open scoped BigOperators

theorem algebra_5055 {x : ℚ} (hx : x > 0) (h : x = 4 / (3 + 4 / (3 + 4 / (3 + x)))) : x = 1 := by
  have h1 : x ≠ 0 := by linarith
  field_simp [h1] at h ⊢
  have h2 : (x - 1) * (x + 4) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- case where $x - 1 = 0$, i.e., $x = 1$
    linarith
  · -- case where $x + 4 = 0$, i.e., $x = -4$
    have h5 : x = -4 := by
      linarith
    linarith -- contradicts with hx : x > 0