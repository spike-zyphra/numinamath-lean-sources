import Mathlib

theorem algebra_10877 (cost : ℝ → ℝ) (hcost : cost = fun x => 22000 * x) :
    cost (250 / 1000) = 5500 := by
  rw [hcost]
  norm_num