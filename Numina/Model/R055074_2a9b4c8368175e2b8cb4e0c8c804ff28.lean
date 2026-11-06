import Mathlib

theorem algebra_257669 (x : ℝ) (hx : x > 0) (h : 3000 / (1 + x / 3000) = 3000 - 120) :
    x = 125 := by
  have h1 : 1 + x / 3000 ≠ 0 := by
    by_contra h2
    have eq1 : x = -3000 := by
      field_simp at h2 ⊢
      linarith
    linarith [show x > 0 by linarith, show x > 0 by linarith]

  field_simp at h
  nlinarith