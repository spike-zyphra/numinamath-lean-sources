import Mathlib

open Real

theorem inequalities_307738 {x y a b : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ha : 0 < a) (hb : 0 < b) (h : a + b = 1) :
    a * x + b * y ≥ x ^ a * y ^ b := by
  have hb1 : b = 1 - a := by linarith
  rw [hb1]
  have h2 : a * x + (1 - a) * y ≥ x ^ a * y ^ (1 - a) := by
    have h4 : x ^ a * y ^ (1 - a) = (x) ^ a * (y) ^ (1 - a) := by rfl
    rw [h4]
    have h5 : a * x + (1 - a) * y ≥ (x) ^ a * (y) ^ (1 - a) := by
      apply Real.geom_mean_le_arith_mean2_weighted
      all_goals
        try linarith
    linarith
  linarith