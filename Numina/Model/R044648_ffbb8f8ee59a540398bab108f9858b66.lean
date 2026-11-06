import Mathlib

theorem number_theory_45779 (p : ℕ) (hp : Nat.Prime p) (h : p > 5) :
    ¬∃ q : ℕ, Nat.Prime q ∧ q^4 = p - 4 := by
  rintro ⟨q, hq, h1⟩
  have h2 : p = q ^ 4 + 4 := by
    omega
  by_cases h3 : q ≤ 5
  · interval_cases q <;> norm_num at hq h1 h2 <;> all_goals 
    have : ¬ Nat.Prime p := by
      rw [h2]
      norm_num
    contradiction
  · -- q > 5 implies q not divisible by 2,3,5.
    have h4 : q > 5 := by
      by_contra h
      push_neg at h
      linarith
    have h5 : q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by
      by_contra h
      push_neg at h
      have h6 : q % 5 = 0 := by 
        omega
      have h7 : ¬ Nat.Prime q := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ q by omega)
        all_goals omega
      contradiction
    have h8 : (q ^ 4) % 5 = 1 := by 
      have h9 : q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := h5
      rcases h9 with (h9 | h9 | h9 | h9)
      · simp [Nat.pow_mod, h9]
      · simp [Nat.pow_mod, h9]
      · simp [Nat.pow_mod, h9]
      · simp [Nat.pow_mod, h9]
    -- Now to form p % 5 = 0.
    have h9 : p % 5 = 0 := by
      omega
    have h10 : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ p by omega)
      all_goals omega
    contradiction