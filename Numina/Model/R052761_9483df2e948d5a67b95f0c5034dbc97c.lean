import Mathlib

theorem algebra_166015 {x y : ℝ} (h1 : (x + 1) * (y + 1) = 10) (h2 : (x + y) * (x * y + 1) = 25) :
    (x, y) = (4, 1) ∨ (x, y) = (1, 4) := by
  have eq1 : x * y + x + y = 9 := by
    nlinarith
  have h3 : (x + y) ^ 2 - 10 * (x + y) + 25 = 0 := by
    nlinarith [h1, h2]
  have h4 : (x + y - 5) ^ 2 = 0 := by
    nlinarith
  have h5 : x + y = 5 := by
    nlinarith
  have h6 : x * y = 4 := by
    nlinarith [eq1, h5]
  have h7 : x ^ 2 - 5 * x + 4 = 0 := by
    have hsum : x + y = 5 := h5
    have hprod : x * y = 4 := h6
    have : y = 5 - x := by linarith
    rw [this] at hprod
    nlinarith
  have h8 : (x - 1) * (x - 4) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- Case $x - 1 = 0$, so $x = 1$
    have hx1 : x = 1 := by linarith
    have hy1 : y = 4 := by
      linarith [h5, hx1]
    right
    simp [hx1, hy1]
  · -- Case $x - 4 = 0$, so $x = 4$
    have hx2 : x = 4 := by linarith
    have hy2 : y = 1 := by
      linarith [h5, hx2]
    left
    simp [hx2, hy2]