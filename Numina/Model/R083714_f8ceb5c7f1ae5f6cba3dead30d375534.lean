import Mathlib

theorem number_theory_185945 {N : ℕ} (hN : N > 1) :
    1743 % N = 2019 % N ∧ 2019 % N = 3008 % N ↔ N = 23 := by
  constructor
  · -- Forward direction: if the remainders are the same, then N = 23
    intro h
    rcases h with ⟨h₁, h₂⟩
    have h3 : N ∣ 276 := by 
      have h4 : (1743 : ℕ) % N = (2019 : ℕ) % N := by linarith 
      have : N ∣ (2019 - 1743 : ℕ) := by
        exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq (by
          omega 
        ) )
      norm_num at this ⊢ 
      exact this

    have h4 : N ∣ 989 := by 
      have h5 : (2019 : ℕ) % N = (3008 : ℕ) % N := by linarith 
      have : N ∣ (3008 - 2019 : ℕ) := by
        exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq (by
          omega 
        ) )
      norm_num at this ⊢ 
      exact this

    have h5 : N ∣ 23 := by 
      exact Nat.dvd_gcd h3 h4 
    have h6 : N ≤ 23 := by 
      exact Nat.le_of_dvd (show (23 : ℕ) > 0 by norm_num) h5 
    interval_cases N <;> norm_num at h₁ h₂ <;> try { tauto } <;> contradiction 

  · -- Backward direction: If N = 23 then the remainders are the same 
    intro h_eq 
    rw [h_eq] 
    constructor 
    · -- Show that 1743 % 23 = 2019 % 23
      norm_num 
    · -- Show that 2019 % 23 = 3008 % 23 
      norm_num