import Mathlib

theorem algebra_1786
  {a r : ℚ}
  (hr : r ≠ 0)
  (h1 : a + a * r = 7)
  (h2 : a + a * r + a * r^2 + a * r^3 + a * r^4 + a * r^5 = 91) :
  a + a * r + a * r^2 + a * r^3 = 28 := by
  have h3 : a * (1 + r) = 7 := by
    linarith
  have h4 : a + a * r + a * r^2 + a * r^3 + a * r^4 + a * r^5 = (a + a * r) + r^2 * (a + a * r) + r^4 * (a + a * r) := by
    ring
  rw [h4] at h2
  have h5 : (a + a * r) * (1 + r^2 + r^4) = 91 := by
    nlinarith
  have h6 : 1 + r^2 + r^4 = 13 := by
    rw [show a + a * r = 7 by linarith [h1]] at h5
    nlinarith
  have h7 : r^4 + r^2 - 12 = 0 := by
    nlinarith
  have h8 : r^2 = 3 := by
    have h9 : r^4 + r^2 - 12 = 0 := h7
    have h10 : r^4 + r^2 - 12 = (r^2 - 3) * (r^2 + 4) := by
      nlinarith
    rw [h10] at h9
    cases (mul_eq_zero.mp h9) with
    | inl h11 =>
      linarith
    | inr h12 =>
      nlinarith [sq_nonneg r]
  have h9 : a + a * r + a * r^2 + a * r^3 = a * (1 + r) * (1 + r^2) := by 
    ring
  rw [h9]
  rw [show a * (1 + r) = 7 by linarith [h3]]
  rw [show r^2 = 3 by linarith [h8]]
  all_goals norm_num