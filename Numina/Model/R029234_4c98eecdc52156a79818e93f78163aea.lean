import Mathlib

theorem number_theory_8368 : (Nat.floor ((10 ^ 20000 : ℝ): ℝ) / (10 ^ 100 + 3)) % 10 = 3 := by
  have h1 : Nat.floor ((10 ^ 20000 : ℝ) / (10 ^ 100 + 3)) = (10 ^ 20000) / (10 ^ 100 + 3) := by
    norm_num [Nat.floor_eq_iff]
  have h5_mod : (Nat.floor ((10^20000 : ℝ) / (10^100 + 3)) ) % 10 = 3 := by
    rw [h1]
    norm_num
  norm_num [h1, h5_mod]