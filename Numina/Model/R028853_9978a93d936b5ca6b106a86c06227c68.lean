import Mathlib

theorem algebra_301320 {x y z : ℝ} (h1 : x * (y + z - x) = 39) (h2 : 2 * x ^ 2 = y * (z + x - y)) (h3 : 2 * y ^ 2 = (x + y - z) + 78 - 2 * z ^ 2) :
    (x, y, z) = (3, 4, 6) ∨ (x, y, z) = (-3, -4, -6) := by

  have h4 : (x - 3) * (x + 3) = 0 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 4), sq_nonneg (z - 6), 
      sq_nonneg (x + 3), sq_nonneg (y + 4), sq_nonneg (z + 6)]
  
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case x = 3.
    have hx : x = 3 := by linarith
    have eq1 : y = 4 := by
      rw [hx] at h1 h2 h3
      nlinarith [sq_nonneg (y - 4), sq_nonneg (z - 6)]
    
    have eq2 : z = 6 := by
      rw [hx, eq1] at h1 h2 h3
      nlinarith
  
    left
    simp [hx, eq1, eq2]

  · -- Case x = -3.
    have hx : x = -3 := by linarith
    have eq1 : y = -4 := by
      rw [hx] at h1 h2 h3
      nlinarith [sq_nonneg (y + 4), sq_nonneg (z + 6)]
    
    have eq2 : z = -6 := by
      rw [hx, eq1] at h1 h2 h3
      nlinarith
  
    right
    simp [hx, eq1, eq2]