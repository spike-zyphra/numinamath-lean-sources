import Mathlib

theorem number_theory_229059 : (Nat.floor (10^1000000 * (1 / 41 : ℝ)) % 10) = 9 := by
  have h1 : Nat.floor (10^1000000 * (1 / 41 : ℝ)) = (10^1000000) / 41 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num