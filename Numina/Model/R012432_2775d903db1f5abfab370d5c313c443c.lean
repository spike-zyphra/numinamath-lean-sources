import Mathlib

theorem number_theory_98141 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : p + q = 85) :
    p * q = 166 := by
  have h1 : p ≤ 85 := by
    linarith
  have h2 : q ≤ 85 := by
    linarith
  by_cases h3 : p % 2 = 1
  · -- Assume p is odd
    have h4 : q % 2 = 0 := by
      omega
    have h5 : q % 2 = 0 := h4
    -- Now q must be even and prime, so q = 2
    have h6 : q = 2 := by
      by_cases h7 : q > 2
      · -- Assume q > 2
        have h8 : q % 2 = 0 := h5
        have h9 : ¬q.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega) (by omega) (by omega)
        contradiction
      interval_cases q <;> try { tauto }
    have h7 : p = 83 := by
      linarith
    rw [h7, h6]
    all_goals norm_num
  · -- Assume p is even (p % 2 = 0)
    have h8 : p % 2 = 0 := by
      omega
    -- Now p must be even and prime, so p = 2
    have h9 : p = 2 := by
      by_cases h11 : p > 2
      · -- Assume p > 2
        have h12 : p % 2 = 0 := h8
        have h13 : ¬p.Prime := by 
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
        contradiction
      interval_cases p <;> try { tauto }
    -- Therefore, q = 85 - 2 = 83
    have h10 : q = 83 := by
      linarith
    rw [h9, h10]
    all_goals norm_num