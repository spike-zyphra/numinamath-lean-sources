import Mathlib

theorem number_theory_271686 {a : ℕ} (ha : Nat.Prime (a - 1)) (hb : Nat.Prime (a + 1))
    (hc : a - 1 > 10) (hd : a + 1 > 10) :
    120 ∣ a^3 - 4 * a := by
  have h1 : a % 2 = 0 := by
    by_contra h
    push_neg at h
    have h2 : a % 2 = 1 := by omega
    have h3 : (a - 1) % 2 = 0 := by
      omega
    have h4 : (a + 1) % 2 = 0 := by
      omega
    have h5 : (a - 1) > 2 := by
      omega
    have h6 : (a + 1) > 2 := by
      omega
    have h7 : ¬ Nat.Prime (a - 1) := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (a - 1) by omega)
      all_goals omega
    have h8 : ¬ Nat.Prime (a + 1) := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (a + 1) by omega)
      all_goals omega
    contradiction
  have h2 : a % 3 = 0 := by
    by_contra h
    push_neg at h
    have h3 : a % 3 = 1 ∨ a % 3 = 2 := by
      omega
    rcases h3 with (h | h)
    · -- Suppose a % 3 = 1
      have h4 : (a - 1) % 3 = 0 := by
        omega
      have h5 : (a - 1) > 3 := by
        omega
      have h6 : ¬ Nat.Prime (a - 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (a - 1) by omega)
        all_goals omega
      contradiction
    · -- Suppose a % 3 = 2
      have h7 : (a + 1) % 3 = 0 := by
        omega
      have h8 : (a + 1) > 3 := by
        omega
      have h9 : ¬ Nat.Prime (a + 1) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (a + 1) by omega)
        all_goals omega
      contradiction
  have h11 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
  have h5ne1 : a % 5 ≠ 1 := by
    by_contra h
    have h6 : (a - 1) % 5 = 0 := by
      omega
    have h7 : (a - 1) > 5 := by
      omega
    have h8 : ¬ Nat.Prime (a - 1) := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (a - 1) by omega)
      all_goals omega
    contradiction
  have h5ne4 : a % 5 ≠ 4 := by
    by_contra h
    have h8 : (a + 1) % 5 = 0 := by
      omega
    have h9 : (a + 1) > 5 := by
      omega
    have h10 : ¬ Nat.Prime (a + 1) := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ (a + 1) by omega)
      all_goals omega
    contradiction
  have h7 : (a ^ 3 - 4 * a) % 3 = 0 := by
    have h8 : a % 3 = 0 := h2
    have : a ^ 3 % 3 = 0 := by
      simp [Nat.pow_mod, h8]
    omega
  have h8 : (a ^ 3 - 4 * a) % 5 = 0 := by
    have h9 : a % 5 = 0 ∨ a % 5 = 2 ∨ a % 5 = 3 := by
      omega
    rcases h9 with (h | h | h) <;> simp [Nat.pow_mod, Nat.mul_mod, h, Nat.add_mod, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq]
  have h10 : (a ^ 3 - 4 * a) % 8 = 0 := by
    have h1 : a % 2 = 0 := h1
    have h13 : a % 8 = 0 ∨ a % 8 = 2 ∨ a % 8 = 4 ∨ a % 8 = 6 := by
      omega
    rcases h13 with (h | h | h | h) <;> simp [Nat.pow_mod, Nat.mul_mod, h, Nat.add_mod, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq]
  omega