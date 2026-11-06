import Mathlib

theorem algebra_197419 (x y : ℝ)
    (h1 : 24 * x ^ 2 - 25 * x * y - 73 * x + 25 * y - 35 = 0)
    (h2 : x ^ 2 - y ^ 2 - 2 * x - 2 * y - 7 = 0) :
    (x, y) = (5, 2) ∨ (x, y) = (-3, -4) := by
  have h3 : ((x - 5) * (x + 3) = 0) := by
    nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 2), sq_nonneg (x + 3), sq_nonneg (y + 4)]
    <;> nlinarith
  cases' (mul_eq_zero.mp h3) with h31 h32
  · -- Let's first handle the case when (x - 5) = 0, which means x = 5
    have hx1 : x = 5 := by linarith
    have hy1 : y = 2 := by
      rw [hx1] at h1
      nlinarith
    left
    simp [hx1, hy1]
  · -- Now handle the case when (x + 3) = 0, which means x = -3
    have hx2 : x = -3 := by linarith
    have hy2 : y = -4 := by
      rw [hx2] at h1
      nlinarith
    right
    simp [hx2, hy2]