import Mathlib

theorem inequalities_104164
    (x y z t : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (ht : 0 < t)
    (h1 : x * z = 20)
    (h2 : y * t = 20) :
    (x + 4) * (y + 4) * (z + 5) * (t + 5) ≥ 80^2 := by 
  nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 4), sq_nonneg (z - 5), sq_nonneg (t - 5),
            mul_pos hx hy, mul_pos hx hz, mul_pos hx ht, mul_pos hy hz, mul_pos hy ht, mul_pos hz ht,
            h1, h2, 
            sq_nonneg (x * z - 20), sq_nonneg (y * t - 20)]