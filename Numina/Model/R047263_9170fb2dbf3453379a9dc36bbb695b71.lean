import Mathlib

theorem number_theory_196125 : IsGreatest {n | 0 < n ∧ 81849 % n = 106392 % n ∧ 106392 % n = 124374 % n} 243 := by
  constructor
  · -- Show 243 is in the set
    constructor
    · norm_num -- 0 < 243
    constructor
    · norm_num -- 81849 % 243 = 106392 % 243
    · norm_num -- 106392 % 243 = 124374 % 243
  · -- Show that 243 is greatest in the set
    intro n hn
    rcases hn with ⟨hn_pos, h1, h2⟩
    by_contra h
    push_neg at h 
    have h3 : n > 243 := h
    have h4 : n ∣ 24543 := by 
      have h5 : (106392 % n) = (81849 % n) := by 
        omega 
      have h6 : n ∣ (106392 - 81849) := by 
        exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h5)
      have h7 : (106392 - 81849 : ℕ) = 24543 := by 
        norm_num 
      rw [h7] at h6 
      exact h6 
    have h8 : n ∣ 17982 := by 
      have h9 : (124374 % n) = (106392 % n) := by 
        omega 
      have h10 : n ∣ (124374 - 106392) := by 
        exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h9)
      have h11 : (124374 - 106392 : ℕ) = 17982 := by 
        norm_num 
      rw [h11] at h10 
      exact h10 
    have h5 : n ∣ 243 := by 
      exact Nat.dvd_gcd h4 h8 
    have h6 : n ≤ 243 := by 
      exact Nat.le_of_dvd (by linarith) h5 
    linarith