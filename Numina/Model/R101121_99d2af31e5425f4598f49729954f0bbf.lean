import Mathlib

theorem number_theory_196292 : (Nat.floor (10^1997 * (1 / 7 : ℝ))) % 10 = 5 := by
  have h1 : Nat.floor (10^1997 * (1 / 7 : ℝ)) = (10^1997 - 5) / 7 := by
    norm_num [Nat.floor_eq_iff]
    <;> omega
  rw [h1]
  norm_num