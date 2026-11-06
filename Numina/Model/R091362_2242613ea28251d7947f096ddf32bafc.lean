import Mathlib

theorem number_theory_15417 : (Nat.floor (10^3 * (3 / 16 : ℝ)) % 10) = 7 := by
  have h1 : Nat.floor (10^3 * (3 / 16 : ℝ)) = 187 := by
    norm_num [Nat.floor_eq_iff]
    <;> linarith
  calc
    Nat.floor (10^3 * (3 / 16 : ℝ)) % 10 = 187 % 10 := by rw [h1]
    _ = 7 := by norm_num