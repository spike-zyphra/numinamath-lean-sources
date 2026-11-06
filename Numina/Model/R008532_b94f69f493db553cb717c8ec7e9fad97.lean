import Mathlib

theorem algebra_12858 {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h1 : r^2 + s^2 = 1) (h2 : r^4 + s^4 = 7 / 8) :
    r * s = 1 / 4 := by
  have eq1 : r^4 + s^4 = (r^2 + s^2) ^ 2 - 2 * (r * s) ^ 2 := by 
    ring_nf
  rw [h1] at eq1
  rw [h2] at eq1
  have eq2 : (r * s) ^ 2 = 1 / 16 := by 
    nlinarith 
  have h3 : r * s > 0 := mul_pos hr hs
  have h4 : r * s = 1 / 4 := by
    nlinarith [sq_nonneg (r * s - 1 / 4), sq_nonneg (r * s + 1 / 4), h3]
  exact h4