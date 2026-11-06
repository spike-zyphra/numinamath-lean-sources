import Mathlib

theorem number_theory_14959 : (Nat.floor (10^534 * (5 / 13 : ℝ)) % 10 = 5) := by
  have h1 : Nat.floor (10^534 * (5 / 13 : ℝ)) = (10^534 * 5 / 13 : ℕ) := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num