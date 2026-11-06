import Mathlib

open Real
open scoped BigOperators

theorem inequalities_39684 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hxy : x < y) (hyz : y < z) (p s d : ℝ)
  (hp : p = 4 * (x + y + z)) (hs : s = 2 * (x * y + y * z + z * x))
  (hd : d = sqrt (x ^ 2 + y ^ 2 + z ^ 2)) :
  x < (p / 4 - sqrt (d ^ 2 - s / 2)) / 3 ∧
  z > (p / 4 - sqrt (d ^ 2 - s / 2)) / 3 := by
  have h2 : p / 4 = x + y + z := by
    rw [hp]
    ring
  have h3 : s / 2 = x * y + y * z + z * x := by
    rw [hs]
    ring
  have h4 : d ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
    rw [hd]
    rw [Real.sq_sqrt]
    positivity
  constructor
  · -- Prove first part.
    have h5 : d ^ 2 - s / 2 = (x ^ 2 + y ^ 2 + z ^ 2) - (x * y + y * z + z * x) := by
      rw [h4, h3]
    have h6 : sqrt (d ^ 2 - s / 2) ^ 2 = d ^ 2 - s / 2 := by
      have h7 : d ^ 2 - s / 2 ≥ 0 := by
        rw [h5]
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
      rw [Real.sq_sqrt]
      all_goals linarith
    rw [h2]
    nlinarith [Real.sqrt_nonneg (d ^ 2 - s / 2), Real.sq_sqrt (show (d ^ 2 - s / 2) ≥ 0 by
      nlinarith [h5, sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    ), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      h2, h5, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      sq_nonneg (sqrt (d ^ 2 - s / 2) - (y + z - 2*x)), 
      mul_pos (show 0 < y - x by linarith) (show 0 < z - y by linarith)]
  · -- Prove second part.
    have h5 : d ^ 2 - s / 2 = (x ^ 2 + y ^ 2 + z ^ 2) - (x * y + y * z + z * x) := by
      rw [h4, h3]
    have h6 : sqrt (d ^ 2 - s / 2) ^ 2 = d ^ 2 - s / 2 := by
      have h7 : d ^ 2 - s / 2 ≥ 0 := by
        rw [h5]
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
      rw [Real.sq_sqrt]
      all_goals linarith
    rw [h2]
    nlinarith [Real.sqrt_nonneg (d ^ 2 - s / 2), Real.sq_sqrt (show (d ^ 2 - s / 2) ≥ 0 by
      nlinarith [h5, sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    ), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      h2, h5, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      sq_nonneg (sqrt (d ^ 2 - s / 2) - (y + z - 2*x)), 
      mul_pos (show 0 < y - x by linarith) (show 0 < z - y by linarith)]