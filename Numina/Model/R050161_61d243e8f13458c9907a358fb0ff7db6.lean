import Mathlib

theorem number_theory_275856 (a b : ℕ) (ha : Odd a) (hb : Odd b) :
    8 ∣ (a^2 - b^2) := by
  have h1 : a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 := by
    rcases ha with ⟨k, hk⟩
    omega
  have h2 : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by
    rcases hb with ⟨k, hk⟩
    omega
  have h3 : a^2 % 8 = 1 := by
    rcases h1 with (h | h | h | h)
    · -- case a % 8 = 1
      simp [Nat.pow_mod, h]
    · -- case a % 8 = 3
      simp [Nat.pow_mod, h]
    · -- case a % 8 = 5
      simp [Nat.pow_mod, h]
    · -- case a % 8 = 7
      simp [Nat.pow_mod, h]
  have h4 : b^2 % 8 = 1 := by
    rcases h2 with (h | h | h | h)
    · -- case b % 8 = 1
      simp [Nat.pow_mod, h]
    · -- case b % 8 = 3
      simp [Nat.pow_mod, h]
    · -- case b % 8 = 5
      simp [Nat.pow_mod, h]
    · -- case b % 8 = 7
      simp [Nat.pow_mod, h]
  have h7 : (a^2 - b^2) % 8 = 0 := by
    omega
  exact Nat.dvd_of_mod_eq_zero h7