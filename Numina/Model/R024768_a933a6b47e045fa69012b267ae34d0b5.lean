import Mathlib

theorem algebra_268640 (cost : ℝ → ℝ) (hcost : cost = fun x => x * 1.20) (avg : ℝ) (havg : avg = 12.5) (d : ℝ) (hd : d = 50) :
    cost (d / avg) = 4.80 := by 
  rw [hcost, havg, hd]
  norm_num