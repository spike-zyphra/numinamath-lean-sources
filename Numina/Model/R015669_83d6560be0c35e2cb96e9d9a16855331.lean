import Mathlib

theorem algebra_322446 (a : ℝ) (h : ∀ x : ℝ, x^3 + (1 - a) * x^2 - 2 * a * x + a^2 = 0 → x = -1 / 4) :
    a < -1 / 4 := by

  have h1 := h a (by
    nlinarith [sq_nonneg (a), sq_nonneg (a - a), sq_nonneg (a + a)]
  )

  have ha : a = -1 / 4 := by linarith

  have h2 := h (-1 / 2) (by
    rw [ha]
    norm_num
  )

  nlinarith