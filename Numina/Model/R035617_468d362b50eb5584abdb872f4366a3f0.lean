import Mathlib

theorem algebra_21750 (cost : ℝ) (annual_cost : ℝ) (savings : ℝ)
    (hcost : cost = 10000) (hanual_cost : annual_cost = 650) (hsavings : savings = 1200) :
    ⌈cost / (savings - annual_cost)⌉ = 19 := by
  rw [hcost, hanual_cost, hsavings]
  norm_num [Int.ceil_eq_iff]