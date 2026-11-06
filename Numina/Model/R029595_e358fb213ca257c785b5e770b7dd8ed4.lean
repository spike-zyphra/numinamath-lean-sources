import Mathlib

theorem number_theory_97885 : (Nat.floor (10^26 * (1 / 20^20 : ℝ)) % 10^26 = 0) := by
  have h1 : Nat.floor (10^26 * (1 / 20^20 : ℝ)) = 0 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num