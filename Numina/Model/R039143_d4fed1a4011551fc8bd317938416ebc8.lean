import Mathlib

theorem number_theory_100833 (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : 7 ∣ 2 * a + 3 * b) : 7 ∣ 4 * a^2 + 5 * b^2 := by
  have h1 : (2 * a + 3 * b) % 7 = 0 := by
    omega
  have h2 : a % 7 = 2 * (b % 7) % 7 := by
    have eq1 : (2 * a + 3 * b) % 7 = 0 := h1
    omega
  have h3 : (4 * a^2 + 5 * b^2) % 7 = 0 := by
    have h4 : a % 7 = 2 * (b % 7) % 7 := h2
    have h5 : b % 7 = 0 ∨ b % 7 = 1 ∨ b % 7 = 2 ∨ b % 7 = 3 ∨ b % 7 = 4 ∨ b % 7 = 5 ∨ b % 7 = 6 := by
      omega
    rcases h5 with (h5 | h5 | h5 | h5 | h5 | h5 | h5)
    · -- b % 7 = 0
      simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h4, h5, Nat.mul_mod, Nat.pow_mod]
      all_goals omega
    · -- b % 7 = 1
      simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h4, h5, Nat.mul_mod, Nat.pow_mod]
      all_goals omega
    · -- b % 7 = 2
      simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h4, h5, Nat.mul_mod, Nat.pow_mod]
      all_goals omega
    · -- b % 7 = 3
      simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h4, h5, Nat.mul_mod, Nat.pow_mod]
      all_goals omega
    · -- b % 7 = 4
      simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h4, h5, Nat.mul_mod, Nat.pow_mod]
      all_goals omega
    · -- b % 7 = 5
      simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h4, h5, Nat.mul_mod, Nat.pow_mod]
      all_goals omega
    · -- b % 7 = 6
      simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod, h4, h5, Nat.mul_mod, Nat.pow_mod]
      all_goals omega
  exact Nat.dvd_of_mod_eq_zero h3