import Mathlib

theorem algebra_193378 {x y z : ℝ} (h1 : z * 15.4 = 18.48 * x) (h2 : z = 0.4 * y)
    (h3 : x + y = 400) : x + y + z = 520 := by
  have h4 : y = 400 - x := by linarith
  rw [h4] at h2
  rw [h2] at h1
  norm_num at h1
  have hx : x = 100 := by 
    nlinarith
  have hy : y = 300 := by 
    rw [hx] at h4
    linarith
  have hz : z = 120 := by 
    rw [hx] at h2
    norm_num at h2 ⊢
    linarith
  linarith [hx, hy, hz]