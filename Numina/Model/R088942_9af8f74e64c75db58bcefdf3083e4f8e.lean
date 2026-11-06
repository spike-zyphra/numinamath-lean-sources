import Mathlib

theorem number_theory_217702 :
    IsGreatest {x | ∀ p : ℕ, p.Prime ∧ p > 5 → x ∣ p^4 - 1} 240 := by
  constructor
  · -- Show 240 is in the set
    intro p hp
    rcases hp with ⟨h_prime, hp_gt⟩
    have h1 : p % 2 ≠ 0 := by 
      by_contra h
      have h2 : ¬ p.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) 
          (by omega)
      contradiction 
    -- Show that divisibility of 16
    have h2 : p % 16 = 1 ∨ p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 7 ∨ p % 16 = 9 ∨ p % 16 = 11 ∨ p % 16 = 13 ∨ p % 16 = 15 := by 
      omega
    have h16 : (p ^ 4) % 16 = 1 := by
      rcases h2 with (h | h | h | h | h | h | h | h) <;> norm_num [h, Nat.pow_mod] at *
    have h3 : (p ^ 4) % 3 = 1 := by
      have h1 : p % 3 = 1 ∨ p % 3 = 2 := by 
        by_contra h
        push_neg at h 
        have h2 : p % 3 = 0 := by 
          omega
        have h3 : 3 ∣ p := by 
          omega
        have h4 : ¬ p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt h3 (by omega) (by omega)
        contradiction 
      rcases h1 with (h | h)
      · 
        simp [h, Nat.pow_mod]
      · 
        simp [h, Nat.pow_mod]
    -- Show divisibility by 5
    have h5 : (p ^ 4) % 5 = 1 := by 
      have h1 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by 
        by_contra h 
        push_neg at h 
        have h2 : p % 5 = 0 := by 
          omega 
        have h3 : 5 ∣ p := by 
          omega 
        have h4 : ¬ p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt h3 (by omega) (by omega)
        contradiction 
      rcases h1 with (h | h | h | h)
      · 
        simp [h, Nat.pow_mod]
      · 
        simp [h, Nat.pow_mod]
      · 
        simp [h, Nat.pow_mod]
      · 
        simp [h, Nat.pow_mod]
    -- Using these congruences, show 240 divides p^4 - 1
    have h6 : p ^ 4 % 16 = 1 := by 
      omega
    have h7 : p ^ 4 % 3 = 1 := by 
      omega 
    have h8 : p ^ 4 % 5 = 1 := by 
      omega 
    -- Therefore, 240 divides p^4 - 1
    have h9 : (p ^ 4 - 1) % 16 = 0 := by 
      omega 
    have h10 : (p ^ 4 - 1) % 3 = 0 := by 
      omega 
    have h11 : (p ^ 4 - 1) % 5 = 0 := by 
      omega 
    -- Now we can conclude 240 divides p^4 - 1 
    have h12 : (p ^ 4 - 1) % 240 = 0 := by 
      omega 
    -- Thus 240 divides p^4 - 1
    exact Nat.dvd_of_mod_eq_zero (show (p ^ 4 - 1) % 240 = 0 by omega)
  · -- Show it's greatest
    intro x hx
    have h1 := hx 7 ⟨by norm_num, by norm_num⟩ 
    have h2 := hx 11 ⟨by norm_num, by norm_num⟩ 
    have h3 := hx 13 ⟨by norm_num, by norm_num⟩ 
    have h4 := hx 17 ⟨by norm_num, by norm_num⟩ 
    have h5 : x ∣ 240 := by 
      exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3) h4
    have h6 : x ≤ 240 := by 
      exact Nat.le_of_dvd (by norm_num) h5
    linarith