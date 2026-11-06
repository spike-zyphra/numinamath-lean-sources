import Mathlib

theorem number_theory_270229 : (Nat.floor ((10^20000 / (10^100 + 3)) : ℝ)) % 10 = 3 := by
  have h1 : Nat.floor ((10^20000 / (10^100 + 3) : ℝ)) = (10^20000) / (10^100 + 3) := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num