import Mathlib

theorem number_theory_222184 (p : ℕ) :
    p.Prime ∧ (3 * p ^ 2 + 1).Prime ↔ p = 2 := by
  constructor
  · -- Assume p and 3p^2 + 1 are both primes, prove p = 2
    rintro ⟨h1, h2⟩
    have h3 : p % 2 = 1 ∨ p % 2 = 0 := by
      omega
    rcases h3 with (h3 | h3)
    · -- Case where p is odd (p % 2 = 1)
      have h4 : p ≥ 3 := by
        by_contra h
        push_neg at h
        interval_cases p <;> norm_num at h1 h2 ⊢ <;> try contradiction
      have h5 : (3 * p ^ 2 + 1) % 2 = 0 := by
        have h6 : p % 2 = 1 := h3
        have h7 : (p ^ 2) % 2 = 1 := by
          simp [Nat.pow_mod, h6]
        omega
      have h8 : (3 * p ^ 2 + 1) > 2 := by
        nlinarith [h4]
      have h9 : ¬(3 * p ^ 2 + 1).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (3 * p ^ 2 + 1) by omega) (by nlinarith) (by nlinarith)
      contradiction
    · -- Case where p is even (p % 2 = 0)
      have h4 : p ≤ 2 ∨ p > 2 := by
        omega
      rcases h4 with (h4 | h4)
      · -- Case where p ≤ 2
        interval_cases p <;> norm_num at h1 h2 ⊢ <;> trivial
      · -- Case where p > 2
        have h5 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by linarith) (by linarith)
        contradiction
  · -- Assume p = 2, prove p and 3p^2 + 1 are both primes
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num