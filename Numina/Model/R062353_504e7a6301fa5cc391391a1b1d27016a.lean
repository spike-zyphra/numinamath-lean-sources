import Mathlib

theorem number_theory_965 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (h1 : a > 3) (h2 : b > 3) (h3 : c > 3) :
    3 ∣ a^2 + b^2 + c^2 := by
  have h1' : a % 3 = 1 ∨ a % 3 = 2 := by
    by_contra h
    push_neg at h
    have h4 : a % 3 = 0 := by 
      omega
    have h5 : ¬ a.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ a by omega)
      all_goals linarith
    contradiction 
  have h2' : b % 3 = 1 ∨ b % 3 = 2 := by
    by_contra h
    push_neg at h
    have h4 : b % 3 = 0 := by 
      omega
    have h5 : ¬ b.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ b by omega)
      all_goals linarith
    contradiction 
  have h3' : c % 3 = 1 ∨ c % 3 = 2 := by
    by_contra h
    push_neg at h
    have h4 : c % 3 = 0 := by 
      omega
    have h5 : ¬ c.Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ c by omega)
      all_goals linarith
    contradiction 
  have ha2 : a^2 % 3 = 1 := by
    rcases h1' with (h | h)
    · -- If a % 3 = 1
      norm_num [Nat.pow_mod, h]
    · -- If a % 3 = 2
      norm_num [Nat.pow_mod, h]
  have hb2 : b^2 % 3 = 1 := by
    rcases h2' with (h | h)
    · -- If b % 3 = 1
      norm_num [Nat.pow_mod, h]
    · -- If b % 3 = 2
      norm_num [Nat.pow_mod, h]
  have hc2 : c^2 % 3 = 1 := by
    rcases h3' with (h | h)
    · -- If c % 3 = 1
      norm_num [Nat.pow_mod, h]
    · -- If c % 3 = 2
      norm_num [Nat.pow_mod, h]
  have h4 : (a^2 + b^2 + c^2) % 3 = 0 := by
    omega 
  exact Nat.dvd_of_mod_eq_zero h4