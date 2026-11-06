import Mathlib

theorem number_theory_322895 : (Nat.floor ((10^10000 : ℝ) / (10^100 + 9)) % 10) = 1 := by
  have h1 : Nat.floor ((10^10000 : ℝ) / (10^100 + 9)) = (10^10000) / (10^100 + 9) := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num