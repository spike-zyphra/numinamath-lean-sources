import Mathlib

theorem number_theory_23234 : (Nat.floor (10^291 * (1 / 37 : ℝ)) % 10) = 7 := by
  have h1 : (Nat.floor (10^291 * (1 / 37 : ℝ)) : ℕ) = (10^291) / 37 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num