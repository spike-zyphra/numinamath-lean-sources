import Mathlib

theorem number_theory_239403 {n : ℕ} (h : ∃ m, m^2 = n + 1) :
    12 ∣ n * (n + 1) := by 
  rcases h with ⟨m, hm⟩
  have h1 : n = m^2 - 1 := by 
    omega

  have h2 : n * (n + 1) = (m^2 - 1) * m^2 := by 
    rw [h1]
    <;> ring_nf <;> nlinarith [hm]

  -- We need to show divisibility by 4
  have h3 : (n * (n + 1) ) % 4 = 0 := by 
    rw [h2]
    have h4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by 
      omega
    rcases h4 with (h4 | h4 | h4 | h4)
    · -- m % 4 = 0 
      simp [Nat.mul_mod, Nat.add_mod, Nat.sub_mod_eq_zero_of_mod_eq, h4, pow_two, pow_succ, Nat.mul_assoc]
    · -- m % 4 = 1
      simp [Nat.mul_mod, Nat.add_mod, Nat.sub_mod_eq_zero_of_mod_eq, h4, pow_two, pow_succ, Nat.mul_assoc]
    · -- m % 4 = 2
      simp [Nat.mul_mod, Nat.add_mod, Nat.sub_mod_eq_zero_of_mod_eq, h4, pow_two, pow_succ, Nat.mul_assoc]
    · -- m % 4 = 3
      simp [Nat.mul_mod, Nat.add_mod, Nat.sub_mod_eq_zero_of_mod_eq, h4, pow_two, pow_succ, Nat.mul_assoc]

  -- We need to show divisibility by 3
  have h4 : (n * (n + 1) ) % 3 = 0 := by
    rw [h2]
    have h5 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by 
      omega 
    rcases h5 with (h5 | h5 | h5)
    · -- m % 3 = 0 
      simp [Nat.mul_mod, Nat.add_mod, Nat.sub_mod_eq_zero_of_mod_eq, h5, pow_two, pow_succ, Nat.mul_assoc]
    · -- m % 3 = 1
      simp [Nat.mul_mod, Nat.add_mod, Nat.sub_mod_eq_zero_of_mod_eq, h5, pow_two, pow_succ, Nat.mul_assoc]
    · -- m % 3 = 2
      simp [Nat.mul_mod, Nat.add_mod, Nat.sub_mod_eq_zero_of_mod_eq, h5, pow_two, pow_succ, Nat.mul_assoc]

  omega