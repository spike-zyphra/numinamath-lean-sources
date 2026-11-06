import Mathlib

theorem number_theory_310650 (p : ℕ) (hp : p.Prime ∧ p ≠ 3)
    (h2p1 : (2 * p + 1).Prime) : ¬(4 * p + 1).Prime := by
  rcases hp with ⟨h1, h2⟩
  by_contra h
  have h3 : p % 3 = 1 ∨ p % 3 = 2 := by 
    by_contra h
    push_neg at h
    have h4 : p % 3 = 0 := by
      omega
    have h5 : p > 3 := by
      by_contra h6
      push_neg at h6
      interval_cases p <;> norm_num at h1 h2 <;> tauto
    have h6 : ¬ p.Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals
        omega
    contradiction
  rcases h3 with (h3 | h3)
  · -- Assume p ≡ 1 (mod 3)
    have h4 : (2 * p + 1) % 3 = 0 := by
      omega
    have h5 : ¬(2 * p + 1).Prime := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (2 * p + 1) by omega)
      all_goals
        have : p ≥ 2 := Nat.Prime.two_le h1
        omega
    contradiction
  · -- Assume p ≡ 2 (mod 3)
    have h7 : (4 * p + 1) % 3 = 0 := by 
      omega
    have h8 : ¬(4 * p + 1).Prime := by 
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (4 * p + 1) by omega)
      all_goals
        have : p ≥ 2 := Nat.Prime.two_le h1
        omega
    contradiction