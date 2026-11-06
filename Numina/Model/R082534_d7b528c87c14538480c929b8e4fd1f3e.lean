import Mathlib

theorem algebra_257983 (cost : ℝ)      (v : ℝ)      (d : ℝ)      (hcost : cost = 0.75)      (hv : v = 25 / 3)      (hd : d = 600) :
    d / v * cost = 54 := by
  rw [hcost, hv, hd]
  norm_num