import Mathlib

theorem number_theory_94823 (p q r : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime)
    (hsum : p + q = r) (hord : 1 < p ∧ p < q) :
    p = 2 := by
  rcases hpqr with ⟨hp, hq, hr⟩
  have hp2 : p = 2 := by
    by_cases h : p % 2 = 1
    · -- Assume p is odd, then q and r must be even.
      have h1 : q % 2 = 1 := by
        by_contra h1
        have h1' : q % 2 = 0 := by omega
        have h2 : q > 2 := by
          have h3 : p > 1 := hord.1
          have h4 : p < q := hord.2
          omega
        have h3 : q ≠ 2 := by linarith
        have h4 : q % 2 = 0 := h1'
        have h6 : ¬q.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
          all_goals linarith
        contradiction
      have h2 : r % 2 = 0 := by
        omega
      have h3 : r > 2 := by
        have h4 : p > 1 := hord.1
        have h5 : p < q := hord.2
        have h7 : p + q > 2 := by
          nlinarith
        linarith [hsum, h7]
      have h4 : r % 2 = 0 := h2
      have : ¬r.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ r by omega)
        all_goals 
          linarith
      contradiction
    · -- Assume p is even
      have : p % 2 = 0 := by 
        omega
      by_cases hp1 : p > 2
      · -- Assume p > 2, then ¬p.Prime
        have h1 : p % 2 = 0 := by omega
        have h3 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals 
            omega
        contradiction
      interval_cases p <;> norm_num at hp ⊢
  exact hp2