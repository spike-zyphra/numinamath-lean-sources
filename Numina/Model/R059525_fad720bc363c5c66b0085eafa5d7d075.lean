import Mathlib

theorem number_theory_18694 : (Nat.floor ((9 / 160 : ℝ) * 100)) % 10 = 5 := by
  have h1 : Nat.floor ((9 / 160 : ℝ) * 100) = 5 := by
    norm_num [Nat.floor_eq_iff]
  calc
    (Nat.floor ((9 / 160 : ℝ) * 100)) % 10 = (5) % 10 := by rw [h1]
    _ = 5 := by norm_num