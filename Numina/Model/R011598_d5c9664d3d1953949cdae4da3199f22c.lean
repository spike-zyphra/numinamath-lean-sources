import Mathlib.Tactic

open Finset Real


theorem inequalities_139508 :
    let sum := ∏ i ∈ range 999, ((2*i+1)/(2*i+2) : ℝ)
    1/44 > sum ∧ sum > 1/1999 := by 
  intro sum
  constructor
  · -- Show that 1/44 > sum
    norm_num [sum, prod_range_succ]
  · -- Show that sum > 1/1999
    norm_num [sum, prod_range_succ]