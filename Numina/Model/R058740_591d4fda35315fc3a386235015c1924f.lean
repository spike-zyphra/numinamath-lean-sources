import Mathlib

theorem algebra_17078 (milk : ℝ) (hmilk : milk = 1 / 5) (rachel_drink : ℝ) (hrachel_drink : rachel_drink = milk * (2 / 3)) : rachel_drink = 2 / 15 := by 
  rw [hrachel_drink, hmilk] 
  norm_num