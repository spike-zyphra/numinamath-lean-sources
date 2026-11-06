import Mathlib

theorem algebra_116563 {x y : ℝ} (h1 : x * y + x + 1 = 7 * y) (h2 : x ^ 2 * y ^ 2 + x * y + 1 = 13 * y ^ 2) :
    (x, y) = (3, 1) ∨ (x, y) = (1, 1 / 3) := by
  have h3 : (x - 3) * (x - 1) = 0 := by 
    nlinarith [sq_nonneg (x * y - 3), sq_nonneg (x - 3), sq_nonneg (y - 1), 
      sq_nonneg (x - 1), sq_nonneg (y - 1 / 3), 
      sq_nonneg (x * (y - 1) ), sq_nonneg ((y - 1 / 3) * (y - 1) ), 
      sq_nonneg (y * (x - 1) ), sq_nonneg ((x - 3) * (y - 1 / 3) )
    ]
  cases' (mul_eq_zero.mp h3) with hx1 hx2 
  · -- x - 3 = 0 
    have hx : x = 3 := by linarith 
    have hy : y = 1 := by 
      rw [hx] at h1 
      nlinarith 
    left 
    simp [hx, hy] 
  · -- x - 1 = 0 
    have hx : x = 1 := by linarith 
    have hy : y = 1 / 3 := by 
      rw [hx] at h1 
      nlinarith 
    right 
    simp [hx, hy]