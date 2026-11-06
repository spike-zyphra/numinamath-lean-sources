import Mathlib

theorem algebra_65302 {d v1 v2 : ℝ} (hd : d = 45) (hv1 : v1 = 18) (hv2 : v2 = 12) {x t : ℝ}
    (h1 : x = v1 * t) (h2 : x = d - v2 * t) : x = 27 := by 
  rw [hv1] at h1
  rw [hd, hv2] at h2
  linarith