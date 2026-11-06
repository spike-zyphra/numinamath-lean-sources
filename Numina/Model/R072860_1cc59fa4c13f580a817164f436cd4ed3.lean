import Mathlib

theorem number_theory_17127 : (Nat.floor (10^10 * (1 / 2^10 : ℝ)) % 10 = 5) := by
  have h₁ : (Nat.floor (10^10 * (1 / 2^10 : ℝ)) : ℕ) = 9765625 := by
    norm_num [Nat.floor_eq_iff]
  calc
    Nat.floor (10^10 * (1 / 2^10 : ℝ)) % 10 
        = 9765625 % 10 := by 
          rw [h₁]
    _ = 5 := by norm_num