import Mathlib

theorem algebra_160725 {x y : ℝ} (h1 : x^2 * y - x * y^2 - 3 * x + 3 * y + 1 = 0)
    (h2 : x^3 * y - x * y^3 - 3 * x^2 + 3 * y^2 + 3 = 0) :
    (x, y) = (2, 1) := by
  have eq1 : (x - y) * (x * y - 3) + 1 = 0 := by
    nlinarith
  have eq2 : (x - y) * (x + y) * (x * y - 3) + 3 = 0 := by 
    nlinarith
  have h3 : (x - y) * (x * y - 3) = -1 := by
    linarith
  have h4 : (x + y) * ((x - y) * (x * y - 3)) + 3 = 0 := by 
    nlinarith
  rw [h3] at h4
  have h5 : x + y = 3 := by
    nlinarith
  have h6 : y = 3 - x := by
    linarith
  rw [h6] at eq1
  have h7 : 2 * x^3 - 9 * x^2 + 15 * x - 10 = 0 := by
    ring_nf at eq1 ⊢
    nlinarith
  have h8 : (x - 2) * (2 * x^2 - 5 * x + 5) = 0 := by
    nlinarith [h7]
  cases' (mul_eq_zero.mp h8) with h9 h10
  · 
    have hx : x = 2 := by linarith
    have hy : y = 1 := by
      rw [hx] at h6
      linarith
    simp [hx, hy]
  · 
    have h11 : 2 * x^2 - 5 * x + 5 = 0 := by 
      nlinarith
    nlinarith [sq_nonneg (x - 5 / 4)]