import Mathlib

theorem algebra_211025 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : (28 * y + 42 * x) / (28 * x + 28 * y) = 5 / 3) :
    x / y = 9 / 4 := by
  have h1 : 28 * x + 28 * y > 0 := by
    nlinarith [hx, hy]
  have h2 : 3 * (28 * y + 42 * x) = 5 * (28 * x + 28 * y) := by
    have h3 : (28 * x + 28 * y) > 0 := h1
    field_simp [h3] at h
    nlinarith [h]

  have eq2 : -14 * x - 56 * y = 0 := by
    nlinarith [h2]

  have h3 : x = -4 * y := by
    nlinarith [eq2]

  -- Since $x > 0$, we have $x$ as positive.
  -- From h3: x = -4 * y, with x > 0, contradicts with y > 0
  -- But here using linarith to find contradiction
  have h4 : x < 0 := by
    nlinarith [h3, show y > 0 by linarith [hy]]

  linarith [h4, hx]