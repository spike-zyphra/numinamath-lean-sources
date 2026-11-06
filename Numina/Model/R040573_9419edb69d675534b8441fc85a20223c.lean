import Mathlib

theorem number_theory_186324 : (Nat.floor (10^17 * (10000 / 9899 : ℝ))) % 10 = 5 := by 
  have h1 : Nat.floor (10^17 * (10000 / 9899 : ℝ)) = (10^21 / 9899 : ℕ) := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num