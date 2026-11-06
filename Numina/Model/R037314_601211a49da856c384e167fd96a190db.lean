import Mathlib

theorem number_theory_7449 : (Nat.floor (10^100 * (2002 / 2009 : ℝ)) % 10) + (Nat.floor (10^100 * (1 / 287 : ℝ)) % 10) = 9 := by 
  have h1 : Nat.floor (10^100 * (2002 / 2009 : ℝ)) = (2002 * 10^100) / 2009 := by 
    norm_num [Nat.floor_eq_iff]
  have h2 : Nat.floor (10^100 * (1 / 287 : ℝ)) = (10^100) / 287 := by 
    norm_num [Nat.floor_eq_iff]
  rw [h1, h2]
  norm_num