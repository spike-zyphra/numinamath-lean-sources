import Mathlib

theorem algebra_195679 {x y P : ℝ} (hx : x^2 - 2 * x - P = 0) (hy : y^2 - 2 * y - P = 0)
    (hxy : |x - y| = 12) : P = 35 := by
  have h1 : (x - y) * (x + y - 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- case 1 : $x - y = 0$ implies $x = y$, which contradicts $ |x - y| = 12 $
    have h21 : x = y := by linarith
    rw [show x - y = (x - y) by rfl, h21] at hxy
    norm_num at hxy
  · -- case 2 : $x + y - 2 = 0$ implies $x + y = 2$
    have hsum : x + y = 2 := by linarith
    cases eq_or_eq_neg_of_abs_eq hxy with
    | inl hxy1 =>
      have hx1 : x = 7 := by
        nlinarith
      have hy1 : y = -5 := by
        nlinarith
      nlinarith [hx1, hy1]
    | inr hxy2 =>
      have hx2 : x = -5 := by
        nlinarith
      have hy2 : y = 7 := by
        nlinarith
      nlinarith [hx2, hy2]