import Mathlib

theorem number_theory_235725 {a : ℕ} (ha : a = 10^99 + 6) :
    (Nat.floor (10^99 * (1 / a : ℝ))) % 10 = 0 := by
  rw [ha]
  have h1 : Nat.floor (10 ^ 99 * (1 / (10 ^ 99 + 6 : ℕ) : ℝ)) = 0 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  all_goals norm_num