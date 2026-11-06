import Mathlib

/- George has a quadratic of the form $x^2+bx+\frac13$, where $b$ is a specific negative number. Using his knowledge of how to complete the square, George is able to rewrite this quadratic in the form $(x+m)^2+\frac{1}{12}$. What is $b$? -/
theorem algebra_10298 {b m : ℝ} (hb : b < 0) (h : ∀ x, x ^ 2 + b * x + 1 / 3 = (x + m) ^ 2 + 1 / 12) :
    b = -1 := by
  have h0 := h
  specialize h0 0
  replace h0 : m ^ 2 - (1 / 2) ^ 2 = 0 := by
    linarith only [h0]
  rw [sq_sub_sq, mul_eq_zero] at h0
  obtain h0 | h0 := h0
  . -- If m = -1 / 2, b = -1.
    rw [show m = -1 / 2 by linarith only [h0]] at h
    ring_nf at h
    conv at h =>
      ext x
      rw [show 1 / 3 - x = 1 / 3 + (-x) by ring_nf]
    simp at h
    specialize h 1
    linarith only [h]
  . -- If m = 1 / 2, b is positive, hence rejected.
    rw [show m = 1 / 2 by linarith only [h0]] at h
    ring_nf at h
    simp at h
    specialize h 1
    linarith
