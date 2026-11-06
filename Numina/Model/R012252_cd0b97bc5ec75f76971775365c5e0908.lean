import Mathlib

theorem number_theory_608399 : (7 ^ 2009) % 10 = 7 := by
  calc (7 ^ 2009) % 10 
      = (7 ^ (4 * 502 + 1)) % 10 := by norm_num
      _ = ((7 ^ 4) ^ 502 * 7 ^ 1) % 10 := by rw [Nat.pow_add, Nat.pow_mul]
      _ = ((7 ^ 4) ^ 502 * 7) % 10 := by norm_num
      _ = (1 ^ 502 * 7) % 10 := by rw [show 7 ^ 4 = 2401 by norm_num]; norm_num
      _ = (1 * 7) % 10 := by norm_num
      _ = 7 := by norm_num