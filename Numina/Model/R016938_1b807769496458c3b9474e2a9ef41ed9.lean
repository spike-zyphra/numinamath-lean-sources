import Mathlib

theorem number_theory_90649 (p : ℕ) (hp : Nat.Prime p) (h : p ≡ 1 [MOD 7]) :
    ∃ m > 0, p ∣ m^3 + m^2 - 2 * m - 1 := by
  have h1 : p % 7 = 1 := by 
    norm_num [Nat.ModEq] at h 
    omega
  have h2 : p ≥ 2 := Nat.Prime.two_le hp
  use 1
  constructor
  · -- Show m > 0
    norm_num
  · -- Show p divides 1^3 + 1^2 - 2 * 1 - 1
    have h_eq : (1 : ℕ) ^ 3 + (1 : ℕ) ^ 2 - 2 * (1 : ℕ) - 1 = 0 := by
      omega
    rw [h_eq]
    all_goals
      norm_num