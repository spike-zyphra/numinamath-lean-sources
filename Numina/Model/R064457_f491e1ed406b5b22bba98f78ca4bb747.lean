import Mathlib

theorem algebra_286652 {x y z : ℝ} (h1 : x * y - 2 * y = x + 106) (h2 : y * z + 3 * y = z + 39)
    (h3 : z * x + 3 * x = 2 * z + 438) :
    (x, y, z) = (38, 4, 9) ∨ (x, y, z) = (-34, -2, -15) := by 
  have h4 : (x - 38) * (x + 34) = 0 := by
    nlinarith [sq_nonneg (x - 38), sq_nonneg (y - 4), sq_nonneg (z - 9),
      sq_nonneg (x + 34), sq_nonneg (y + 2), sq_nonneg (z + 15)]
  cases' (mul_eq_zero.1 h4) with h41 h42
  · -- Case 1: x = 38
    have hx : x = 38 := by linarith
    have hy : y = 4 := by
      rw [hx] at h1
      nlinarith
    have hz : z = 9 := by 
      rw [hy] at h2
      nlinarith
    left
    simp [hx, hy, hz]
  · -- Case 2: x = -34
    have hx : x = -34 := by linarith
    have hy : y = -2 := by
      rw [hx] at h1
      nlinarith
    have hz : z = -15 := by 
      rw [hy] at h2
      nlinarith
    right
    simp [hx, hy, hz]