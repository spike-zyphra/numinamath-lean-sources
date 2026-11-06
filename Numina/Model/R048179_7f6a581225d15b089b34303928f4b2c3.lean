import Mathlib

theorem algebra_120939 {x y z : ℝ} (h1 : (x + 1) * y * z = 12) (h2 : (y + 1) * z * x = 4) (h3 : (z + 1) * x * y = 4) :
    (x, y, z) = (2, -2, -2) ∨ (x, y, z) = (1 / 3, 3, 3) := by
  have h4 : x * z = x * y := by
    nlinarith [h1, h2, h3]
  have hxne : x ≠ 0 := by
    by_contra hx
    rw [hx] at h2 h1 h3
    nlinarith 
  have h5 : z = y := by
    apply (mul_left_inj' hxne).mp
    linarith
  rw [show z = y by linarith [h5]] at h1
  have eq1 : (x + 1) * y ^ 2 = 12 := by
    nlinarith 
  have eq2 : (y + 1) * x * y = 4 := by
    rw [show z = y by linarith [h5]] at h2
    nlinarith [h5]
  have h6 : y ^ 2 - x * y = 8 := by
    nlinarith [eq1, eq2]
  have h7 : (y + 2) * (y - 3) = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 2), sq_nonneg (x - 1 / 3), sq_nonneg (y - 3), sq_pos_of_ne_zero (show (1 : ℝ) ≠ 0 by norm_num)]
  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- If $y = -2$, find $x$ from negative coefficients which gives quadratics
    have hy : y = -2 := by linarith 
    have hx : x = 2 := by
      rw [hy] at eq1
      nlinarith
    have h9 : z = -2 := by
      linarith [h5, hy]
    left
    simp [hx, hy, h9]
  · -- If $y = 3$, find $x$ from advantage variables.
    have hy : y = 3 := by linarith 
    have hx : x = 1 / 3 := by
      rw [hy] at eq1
      nlinarith
    have h9 : z = 3 := by
      linarith [h5, hy]
    right
    simp [hx, hy, h9]