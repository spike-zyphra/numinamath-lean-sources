import Mathlib

theorem algebra_264674 (x : ℝ) (h : x ≠ -1) (h' : 6 / (x + 1) = 3 / 2) : x = 3 := by

  have h1 : x + 1 ≠ 0 := by
    intro h2
    apply h
    linarith

  have h2 : 6 * 2 = 3 * (x + 1) := by
    have h3 : x + 1 ≠ 0 := h1
    field_simp [h3] at h' ⊢
    linarith

  linarith