import Mathlib

theorem number_theory_19610 : (Nat.floor (10^453 * (6 / 13 : ℝ)) % 10 = 1) := by
  have h1 : Nat.floor (10^453 * (6 / 13 : ℝ)) = (6 * 10^453) / 13 := by 
    norm_num [Nat.floor_eq_iff]
  calc 
    Nat.floor (10^453 * (6 / 13 : ℝ)) % 10 = ((6 * 10^453) / 13) % 10 := by 
      rw [h1]
    _ = 1 := by 
      norm_num