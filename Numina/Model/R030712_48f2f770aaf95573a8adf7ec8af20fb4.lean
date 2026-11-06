import Mathlib

theorem number_theory_135367 (p : ℕ) (hp : p.Prime) (h : (p^2 + 2).Prime) :
    (p^3 + 2).Prime ∧ (p^3 + 10).Prime ∧ (p^4 + 2).Prime ∧ (p^4 - 2).Prime := by
  by_cases h1 : p ≤ 3
  · interval_cases p <;> norm_num at hp h ⊢ <;> tauto
  · -- p > 3
    push_neg at h1
    have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
      by_contra h
      push_neg at h
      have : p % 3 = 0 := by omega
      have h3 : p > 3 := by linarith
      have h4 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    have h3 : (p ^ 2 + 2) % 3 = 0 := by
      rcases h2 with (h2 | h2)
      · -- p ≡ 1 (mod 3)
        have h4 : p % 3 = 1 := h2
        have hp1 : p ^ 2 % 3 = 1 := by
          simp [Nat.pow_mod, h4]
        omega
      · -- p ≡ 2 (mod 3)
        have h4 : p % 3 = 2 := h2
        have hp1 : p ^ 2 % 3 = 1 := by
          simp [Nat.pow_mod, h4]
        omega
    have h4 : ¬(p ^ 2 + 2).Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p ^ 2 + 2) by omega)
      all_goals
      have hp1 : p ≥ 4 := by
        by_contra h
        push_neg at h
        interval_cases p <;> norm_num at hp h1
      have hp2 : p ^ 2 + 2 > 3 := by 
        nlinarith [hp1]
      all_goals nlinarith [hp2]
    contradiction