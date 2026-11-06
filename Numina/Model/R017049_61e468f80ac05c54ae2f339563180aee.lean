import Mathlib

theorem number_theory_145524 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : |(p : ℤ) - q| = 2) (h1 : p > 3) (h2 : q > 3) :
    12 ∣ p + q := by 
  have h3 : (p : ℤ) - q = 2 ∨ (p : ℤ) - q = -2 := by
    cases' eq_or_eq_neg_of_abs_eq h with h4 h4
    · -- p - q = 2
      left
      linarith
    · -- p - q = -2
      right
      linarith
  cases h3 with
  | inl h4 =>
    -- case p - q = 2 so p = q + 2
    have h5 : (p : ℤ) = q + 2 := by
      linarith
    have h6 : p = q + 2 := by
      norm_cast at h5 ⊢
    have h7 : p % 3 = 1 ∨ p % 3 = 2 := by 
      by_contra hneq
      push_neg at hneq
      have : p % 3 = 0 := by omega
      have : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals linarith
      contradiction
    have h8 : q % 3 = 1 ∨ q % 3 = 2 := by 
      by_contra hneq
      push_neg at hneq
      have : q % 3 = 0 := by omega
      have : ¬q.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
        all_goals linarith
      contradiction
    have h11 : p % 4 = 1 ∨ p % 4 = 3 := by
      by_contra hneq
      push_neg at hneq
      have : p % 2 = 0 := by
        omega
      have : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals linarith
      contradiction
    have h14 : q % 4 = 1 ∨ q % 4 = 3 := by 
      by_contra hneq
      push_neg at hneq
      have : q % 2 = 0 := by 
        omega
      have : ¬q.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
        all_goals linarith
      contradiction
    -- now we need to show $12 | p + q$
    have h20 : (p + q) % 3 = 0 := by
      omega
    have h40 : (p + q) % 4 = 0 := by 
      omega
    omega
  | inr h4 =>
    -- case p - q = -2 so q = p + 2
    have h5 : (q : ℤ) = p + 2 := by
      linarith
    have h8 : q = p + 2 := by
      norm_cast at h5 ⊢
    have h7 : p % 3 = 1 ∨ p % 3 = 2 := by 
      by_contra hneq
      push_neg at hneq
      have : p % 3 = 0 := by omega
      have : ¬p.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals linarith
      contradiction
    have h8 : q % 3 = 1 ∨ q % 3 = 2 := by 
      by_contra hneq
      push_neg at hneq
      have : q % 3 = 0 := by omega
      have : ¬q.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
        all_goals linarith
      contradiction
    have h11 : p % 4 = 1 ∨ p % 4 = 3 := by
      by_contra hneq
      push_neg at hneq
      have : p % 2 = 0 := by
        omega
      have : ¬p.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
        all_goals linarith
      contradiction
    have h14 : q % 4 = 1 ∨ q % 4 = 3 := by
      by_contra hneq
      push_neg at hneq
      have : q % 2 = 0 := by 
        omega
      have : ¬q.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
        all_goals linarith
      contradiction
    -- now we need to show $12 | p + q$
    have h20 : (p + q) % 3 = 0 := by
      omega
    have h40 : (p + q) % 4 = 0 := by
      omega
    omega