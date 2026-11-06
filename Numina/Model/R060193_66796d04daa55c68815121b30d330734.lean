import Mathlib

open Real

theorem inequalities_104842 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≤ 2) (hyz : y ≤ 3) (hzx : x + y + z = 11) :
    sqrt (x * y * z) ≤ 6 := by
  have h1 : z = 11 - x - y := by linarith
  have h2 : x * y * z ≤ 36 := by
    rw [h1]
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 3), sq_nonneg (x + y - 5), 
      hxy, hyz, 
      mul_pos hx hy, 
      mul_pos hx (show 0 < 11 - x - y by nlinarith), 
      mul_pos hy (show 0 < 11 - x - y by nlinarith)
    ]
  have h3 : sqrt (x * y * z) ≤ sqrt (36 : ℝ) := Real.sqrt_le_sqrt (by nlinarith [h2])
  have h4 : sqrt ((36 : ℝ)) = 6 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  linarith [h3, h4]