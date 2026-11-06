import Mathlib

theorem algebra_312428 {x y : ℝ} (hx : x > 0) (hy : y > 0) (h : x^2 - 3 * y^2 = 2 * x * y) :
    (x + 2 * y) / (x - y) = 5 / 2 := by
  have h1 : x^2 - 2 * x * y - 3 * y^2 = 0 := by
    linarith
  have h2 : (x - 3 * y) * (x + y) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case where $x - 3y = 0$, so $x = 3y$
    have h3' : x = 3 * y := by linarith
    have hx1 : x - y > 0 := by
      nlinarith
    have h4' : x + 2 * y = 5 * y := by
      rw [show x = 3 * y by linarith]
      linarith
    have h5' : x - y = 2 * y := by
      rw [show x = 3 * y by linarith]
      linarith
    have h6' : (x + 2 * y) / (x - y) = (5 * y) / (2 * y) := by
      rw [h4', h5']
    have h7' : (5 * y) / (2 * y) = 5 / 2 := by
      have hy1 : y ≠ 0 := by linarith
      field_simp [hy1]
      <;> nlinarith
    rw [h6']
    rw [h7']
  · -- Case where $x + y = 0$, so $x = -y$
    have h4' : x = -y := by linarith
    nlinarith