import Mathlib

theorem number_theory_291301 : 2014 ∣ ∏ i ∈ Finset.range 5, (53 + i) := by 
  norm_num [Finset.prod_range_succ]