import Mathlib

theorem number_theory_211549 (n : ℕ) (h : ∃ p : ℕ, p.Prime ∧ n % 2022 + (n + 1) % 2022 + (n + 2) % 2022 = p) :
    2022 ∣ n ∨ 2022 ∣ n + 1 ∨ 2022 ∣ n + 2 := by 
  rcases h with ⟨p, hp, h1⟩
  by_contra h8
  push_neg at h8
  have h9 : ¬2022 ∣ n := h8.1
  have h10 : ¬2022 ∣ (n + 1) := h8.2.1
  have h11 : ¬2022 ∣ (n + 2) := h8.2.2
  have h12 : n % 2022 > 0 := by
    by_contra h
    push_neg at h
    have : n % 2022 = 0 := by 
      omega 
    have : 2022 ∣ n := by
      omega
    contradiction 
  have h13 : (n + 1) % 2022 > 0 := by
    by_contra h
    push_neg at h
    have : (n + 1) % 2022 = 0 := by 
      omega 
    have : 2022 ∣ (n + 1) := by
      omega 
    contradiction 
  have h14 : (n + 2) % 2022 > 0 := by 
    by_contra h
    push_neg at h 
    have : (n + 2) % 2022 = 0 := by 
      omega 
    have : 2022 ∣ (n + 2) := by 
      omega 
    contradiction 
  have h15 : p = n % 2022 + (n + 1) % 2022 + (n + 2) % 2022 := by 
    omega 
  have h16 : (n + 1) % 2022 = (n % 2022 + 1) % 2022 := by 
    simp [Nat.add_mod] 
  have h17 : (n + 2) % 2022 = (n % 2022 + 2) % 2022 := by
    simp [Nat.add_mod]
  have h18 : p = (n % 2022 + (n % 2022 + 1) % 2022 + (n % 2022 + 2) % 2022) := by 
    rw [h15]
    rw [h16, h17] 
  have h19 : p % 3 = 0 := by 
    have h25 : (n % 2022 + (n % 2022 + 1) % 2022 + (n % 2022 + 2) % 2022) % 3 = 0 := by 
      have h20 : n % 2022 % 3 = 0 ∨ n % 2022 % 3 = 1 ∨ n % 2022 % 3 = 2 := by 
        omega 
      rcases h20 with (h20 | h20 | h20) 
      · -- case n % 2022 % 3 = 0 
        have h112 : ( (n % 2022) + (n % 2022 + 1) % 2022 + (n % 2022 + 2) % 2022 ) % 3 = 0 := by
          omega 
        exact h112 
      · -- case n % 2022 % 3 = 1 
        have h112 : ( (n % 2022) + (n % 2022 + 1) % 2022 + (n % 2022 + 2) % 2022 ) % 3 = 0 := by
          omega 
        exact h112 
      · -- case n % 2022 % 3 = 2
        have h112 : ( (n % 2022) + (n % 2022 + 1) % 2022 + (n % 2022 + 2) % 2022 ) % 3 = 0 := by
          omega 
        exact h112 
    omega 
  have h28 : p ≠ 3 := by
    by_contra h3
    rw [show p = 3 by linarith] at h1 
    have h15c : n % 2022 + (n + 1) % 2022 + (n + 2) % 2022 = 3 := by
      omega
    omega 
  have h29 : ¬ p.Prime := by
    apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega) (by omega) (by omega) 
  contradiction