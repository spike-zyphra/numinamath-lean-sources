import Mathlib

theorem number_theory_278671 : (Nat.floor (10 ^ 2016 * (15 / 37 : ℝ)) % 10) = 5 := by 
  have h1 : Nat.floor (10 ^ 2016 * (15 / 37 : ℝ)) = (15 * 10 ^ 2016) / 37 := by 
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num