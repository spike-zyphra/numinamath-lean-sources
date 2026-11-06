import Mathlib

theorem algebra_216679 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : y = 13.5 - 9 * x) (h' : -y = 24 - 1.5 * x ^ 2) :
    (24 * x + 4 * x) / (24 * y + 4 * y) = 0.2 := by
  have eq1 : y = 13.5 - 9 * x := h

  have eq2 : -y = 24 - 1.5 * x ^ 2 := h'

  have h3 : 1.5 * x ^ 2 + 9 * x - 37.5 = 0 := by
    rw [eq1] at eq2
    norm_num at eq2 ⊢
    nlinarith

  have h4 : 3 * x ^ 2 + 18 * x - 75 = 0 := by
    have h5 : (1.5 * x ^ 2 + 9 * x - 37.5) = 0 := h3
    ring_nf at h5 ⊢
    nlinarith

  have h5 : x ^ 2 + 6 * x - 25 = 0 := by
    nlinarith

  have h6 : y < 0 := by
    nlinarith [sq_nonneg (x + 3), sq_nonneg (y), sq_nonneg (y - 13.5), sq_nonneg (x * y)]

  linarith