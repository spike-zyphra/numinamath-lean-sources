import Mathlib

theorem number_theory_265421 (p : ℕ) (hp : p.Prime) (h1 : (p + 28).Prime) (h2 : (p + 56).Prime) :
    p = 3 := by
  by_cases h : p ≤ 59
  · interval_cases p <;> norm_num at hp h1 h2 ⊢ <;> tauto
  · -- Assume p > 59
    push_neg at h
    have h3 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
      omega
    rcases h3 with (h3 | h3 | h3)
    · -- Assume p % 3 = 0
      have h4 : p % 3 = 0 := by
        omega
      have h5 : p > 3 := by
        omega
      have h6 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    · -- Assume p % 3 = 1
      have h7 : p % 3 = 1 := by
        omega
      have h8 : (p + 56) % 3 = 0 := by
        omega
      have h9 : ¬(p + 56).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 56) by omega)
        all_goals omega
      contradiction
    · -- Assume p % 3 = 2
      have h10 : p % 3 = 2 := by
        omega
      have h11 : (p + 28) % 3 = 0 := by
        omega
      have h12 : ¬(p + 28).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 28) by omega)
        all_goals omega
      contradiction