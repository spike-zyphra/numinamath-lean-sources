import Mathlib

theorem algebra_127491 : (Nat.floor ((6 / 25 : ℝ) ^ 100 * 10 ^ 61)) % 100 = 0 := by
  have h1 : Nat.floor ((6 / 25 : ℝ) ^ 100 * 10 ^ 61) = 0 := by
    norm_num [Nat.floor_eq_iff]
  calc
    (Nat.floor ((6 / 25 : ℝ) ^ 100 * 10 ^ 61)) % 100 = 0 % 100 := by rw [h1]
    _ = 0 := by norm_num