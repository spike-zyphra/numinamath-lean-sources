import Mathlib

theorem number_theory_160285 (p : ℕ) (hp : p.Prime) (hp' : (p + 2).Prime) (hp'' : (p + 4).Prime) :
    p = 3 := by
  by_cases h : p ≤ 3
  · interval_cases p <;> norm_num at hp hp' hp'' ⊢ <;> tauto
  · -- Assume p > 3
    push_neg at h
    have h1 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h1 with (h1 | h1 | h1)
    · -- p % 3 = 0
      have h2 : p % 3 = 0 := h1
      have h3 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega
      contradiction
    · -- p % 3 = 1
      have h2 : (p + 2) % 3 = 0 := by
        omega
      have h3 : ¬(p + 2).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 2) by omega)
        all_goals omega
      contradiction
    · -- p % 3 = 2
      have h2 : (p + 4) % 3 = 0 := by
        omega
      have h3 : ¬(p + 4).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p + 4) by omega)
        all_goals omega
      contradiction