import Mathlib

theorem algebra_237667 {x y : ℝ} (t : ℝ) (h1 : x = 1 + 2 * t - 2 * t ^ 2)
  (h2 : y = 2 * (1 + t) * Real.sqrt (1 - t ^ 2))
  (pos : 0 ≤ (1 - t ^ 2))
  : y ^ 4 + 2 * y ^ 2 * (x ^ 2 - 12 * x + 9) + x ^ 4 + 8 * x ^ 3 + 18 * x ^ 2 - 27 = 0
  := by
    have eq1 : y ^ 2 = 4 * (1 + t) ^ 2 * (1 - t^2) := by
      calc
        y ^ 2 = (2 * (1 + t) * Real.sqrt (1 - t^2) ) ^ 2 := by rw [h2]
        _ = 4 * (1 + t) ^ 2 * (Real.sqrt (1 - t^2) ) ^ 2 := by ring
        _ = 4 * (1 + t) ^ 2 * (1 - t^2) := by
          rw [Real.sq_sqrt]
          linarith
    have eq1' : y ^ 2 = 4 + 8 * t - 8 * t^3 - 4 * t^4 := by
      rw [eq1]
      ring_nf
    have eq2 : y^4 = (4 + 8 * t - 8 * t^3 - 4 * t^4) ^ 2 := by
      calc 
        y^4 = (y ^ 2) ^ 2 := by ring
        _ = (4 + 8 * t - 8 * t^3 - 4 * t^4) ^ 2 := by rw [eq1']
    have eq4 : x = 1 + 2 * t - 2 * t^2 := h1
    have eq3 : x^4 = (1 + 2 * t - 2 * t^2) ^ 4 := by
      rw [eq4]
      all_goals ring_nf
    rw [eq2, eq1', eq4]
    nlinarith [sq_nonneg ((t - 1) * (t + 1)), sq_nonneg ((1 + t) * (t - 1 / 2)), sq_nonneg ((t - 1 / 2) * (t + 1 / 2)), sq_nonneg (t ^ 2 - 1 / 4), mul_nonneg (show 0 ≤ 1 - t ^ 2 by linarith) (show 0 ≤ 1 - t ^ 2 by linarith), sq_nonneg (t ^ 2 -1) ]