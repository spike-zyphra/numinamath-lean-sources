import Mathlib

theorem number_theory_15049 : (Nat.floor (10 ^ 1314 * (5 / 14 : ℝ))) % 10 = 2 := by
  have h1 : Nat.floor (10 ^ 1314 * (5 / 14 : ℝ)) = (5 * 10 ^ 1314) / 14 := by
    norm_num [Nat.floor_eq_iff, mul_add, mul_comm, mul_assoc]
  rw [h1]
  norm_num