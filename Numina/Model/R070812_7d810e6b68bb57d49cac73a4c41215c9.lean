import Mathlib

theorem algebra_10307 : ⌊Real.pi⌋ = 3 := by 
  have h1 : 3 ≤ Real.pi := by 
    linarith [Real.pi_gt_three]
  have h2 : Real.pi < 4 := by 
    linarith [Real.pi_lt_315]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> linarith [Real.pi_gt_three, Real.pi_lt_315]