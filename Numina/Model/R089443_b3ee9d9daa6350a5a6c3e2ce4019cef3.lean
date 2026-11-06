import Mathlib

theorem algebra_21663 {a b : ℤ} (h : ∀ z : ℤ, 2 * z ^ 2 + 13 * z + 21 = (z + a) * (2 * z + b)) :
    2 * a + b = 13 := by
  have eq1 := h 0
  have h1 : a * b = 21 := by
    nlinarith
  
  have h2 : 2 * a + b = 13 := by
    have eq2 := h 1
    have eq3 := h (-1)
    ring_nf at eq2 eq3
    nlinarith [h1]

  linarith