import Mathlib

theorem number_theory_11962 : (Nat.floor ((3 / 1250 : ℝ) * 10 ^ 2)) % 10 ^ 2 = 0 := by
  have h1 : (3 / 1250 : ℝ) * (10 : ℝ) ^ 2 = (0.24 : ℝ) := by 
    norm_num
  have h2 : Nat.floor ((3 / 1250 : ℝ) * (10 : ℝ) ^ 2) = 0 := by
    rw [h1]
    norm_num [Nat.floor_eq_iff]
  calc
    (Nat.floor ((3 / 1250 : ℝ) * (10 : ℝ) ^ 2)) % 10 ^ 2
        = (0 : ℕ) % 10 ^ 2 := by rw [h2]
    _ = 0 := by norm_num