import Mathlib

theorem number_theory_277697 : (Nat.floor (10^1000 * (9 / 28 : ℝ)) % 10) = 4 := by
  have h1 : Nat.floor (10^1000 * (9 / 28 : ℝ)) = (9 * 10^1000) / 28 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num