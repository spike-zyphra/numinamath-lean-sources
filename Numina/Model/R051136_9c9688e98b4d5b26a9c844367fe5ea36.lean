import Mathlib

theorem algebra_13351
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (hxy : x * y = 24)
    (hxz : x * z = 48)
    (hyz : y * z = 72) :
    x + y + z = 22 := by 
  have h1 : x^2 = 16 := by
    nlinarith [hxy, hxz, hyz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have hx_val : x = 4 := by
    nlinarith [h1, show 0 ≤ x by linarith]
  have hy_val : y = 6 := by 
    rw [hx_val] at hxy
    nlinarith 
  have hz_val : z = 12 := by 
    rw [hx_val] at hxz
    nlinarith 
  linarith [hx_val, hy_val, hz_val]