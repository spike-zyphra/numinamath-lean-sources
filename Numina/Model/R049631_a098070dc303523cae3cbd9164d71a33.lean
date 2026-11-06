import Mathlib

theorem algebra_7916 {a b c d x : ℝ} (ha : a = -b) (hc : c * d = 1)
    (hx : |x| = 2) : (a + b) * x^3 + c * d * x^2 + x + 3 = 5 ∨ (a + b) * x^3 + c * d * x^2 + x + 3 = 9 := by
  have h1 : a + b = 0 := by linarith [ha]
  cases eq_or_eq_neg_of_abs_eq hx with
  | inl hx1 =>
    have hx2 : x = 2 := hx1
    have eq9 : (a + b) * x^3 + c * d * x^2 + x + 3 = 9 := by
      rw [show a + b = (0 : ℝ) by linarith [h1]]
      rw [show c * d = (1 : ℝ) by linarith [hc]]
      rw [hx2]
      norm_num
    right
    linarith [eq9]
  | inr hx2 =>
    have hx3 : x = -2 := hx2
    have eq5 : (a + b) * x^3 + c * d * x^2 + x + 3 = 5 := by
      rw [show a + b = (0 : ℝ) by linarith [h1]]
      rw [show c * d = (1 : ℝ) by linarith [hc]]
      rw [hx3]
      norm_num
      <;> nlinarith
    left
    linarith [eq5]