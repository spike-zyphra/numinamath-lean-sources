import Mathlib

theorem number_theory_16410 : (Nat.floor (10 ^ 100 * (1 / 7 : ℝ))) % 10 = 8 := by
  have h1 : Nat.floor (10 ^ 100 * (1 / 7 : ℝ)) = (10 ^ 100 / 7 : ℕ) := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num