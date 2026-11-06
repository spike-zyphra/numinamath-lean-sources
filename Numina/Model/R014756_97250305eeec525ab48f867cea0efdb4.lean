import Mathlib

theorem number_theory_240297 (a b : ℕ) (ha : Nat.Prime a) (hb : Nat.Prime b)
    (h1 : 3 < a) (h2 : 3 < b) :
    12 ∣ (a + b) * (a - b) := by
  have h3 : a % 2 = 1 := by 
    by_contra h
    push_neg at h
    have : a > 2 := by linarith 
    have : ¬Nat.Prime a := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ a by omega) (by omega) (by omega)
    tauto 
  have h4 : b % 2 = 1 := by 
    by_contra h
    push_neg at h
    have : b > 2 := by linarith 
    have : ¬Nat.Prime b := by 
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ b by omega) (by omega) (by omega)
    tauto 
  have h5 : a % 3 = 1 ∨ a % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h6 : a % 3 = 0 := by 
      omega 
    have h7 : a > 3 := by linarith
    have h8 : ¬Nat.Prime a := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ a by omega) (by omega) (by omega)
    tauto 
  have h6 : b % 3 = 1 ∨ b % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h7 : b % 3 = 0 := by 
      omega 
    have h8 : b > 3 := by linarith 
    have h9 : ¬Nat.Prime b := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ b by omega) (by omega) (by omega) 
    tauto 
  have h8 : (a + b) * (a - b) % 3 = 0 := by 
    rcases h5 with (h5 | h5) <;> rcases h6 with (h6 | h6) <;> 
      simp [Nat.add_mod, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq, h5, h6] 
      <;> omega 
  have h9 : (a + b) * (a - b) % 4 = 0 := by 
    have ha1 : a % 2 = 1 := h3
    have hb1 : b % 2 = 1 := h4
    have ha2 : a % 4 = 1 ∨ a % 4 = 3 := by 
      omega 
    have hb2 : b % 4 = 1 ∨ b % 4 = 3 := by 
      omega 
    rcases ha2 with (ha2 | ha2) <;> rcases hb2 with (hb2 | hb2) <;> 
      simp [Nat.add_mod, Nat.mul_mod, Nat.sub_mod_eq_zero_of_mod_eq, ha2, hb2] 
      <;> omega 
  have h10 : 3 ∣ (a + b) * (a - b) := by 
    omega
  have h11 : 4 ∣ (a + b) * (a - b) := by 
    omega
  have h12 : 12 ∣ (a + b) * (a - b) := by 
    omega
  exact h12
  all_goals
  omega
  all_goals
  omega
  all_goals 
  nlinarith 
  all_goals
  omega