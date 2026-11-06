import Mathlib

theorem number_theory_15202 : (Nat.floor (10^111 * (33 / 555 : ℝ))) % 10 = 9 := by
  have h1 : Nat.floor (10^111 * (33 / 555 : ℝ)) = (11 * 10^111) / 185 := by
    norm_num [Nat.floor_eq_iff]
  calc
    Nat.floor (10^111 * (33 / 555 : ℝ)) % 10 = ((11 * 10^111) / 185) % 10 := by
      rw [h1]
    _ = 9 := by
      norm_num