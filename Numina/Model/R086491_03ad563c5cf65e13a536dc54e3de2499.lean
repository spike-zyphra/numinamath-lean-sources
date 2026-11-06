import Mathlib

theorem number_theory_7163 : (Nat.floor (10^35 * (1 / 71 : ℝ)) % 1000) = 169 := by
  have h1 : Nat.floor (10^35 * (1 / 71 : ℝ)) = (10^35) / 71 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num