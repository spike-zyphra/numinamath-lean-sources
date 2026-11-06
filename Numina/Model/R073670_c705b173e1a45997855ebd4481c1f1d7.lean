import Mathlib

theorem number_theory_266686 : (Nat.floor (10^100 * (1 / 7 : ℝ))) % 10 = 8 := by 
  have h1 : Nat.floor (10^100 * (1 / 7 : ℝ)) = (10^100 - 4) / 7 := by 
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num