import Mathlib

theorem number_theory_178871 (p q r : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime) (h : 2 * p + 3 * q = 6 * r) :
    p + q + r = 7 := by 
  rcases hpqr with ⟨hp, hq, hr⟩
  have h1 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by 
    omega
  have h2 : (2 * p + 3 * q) % 3 = (6 * r) % 3 := by
    omega 
  have h3 : (2 * p) % 3 = 0 := by 
    omega
  have h4 : p % 3 = 0 := by 
    omega
  have hp3 : p = 3 := by 
    by_cases h5 : p > 3 
    · -- Assume p > 3
      have h6 : ¬p.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega 
      tauto 
    · -- Assume ¬(p > 3)
      interval_cases p <;> norm_num at hp ⊢ <;> tauto 
  have h5 : 2 * 3 + 3 * q = 6 * r := by 
    rw [show p = 3 by omega] at h 
    linarith
  -- 3 * q = 6 * (r - 1)
  have h6 : 3 * q = 6 * (r - 1) := by 
    omega 
  -- From this, q must be even.
  have h7 : q % 2 = 0 := by 
    omega 
  have hq2 : q = 2 := by 
    by_cases h9 : q > 2 
    · -- Assume q > 2 
      have h10 : ¬q.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
        all_goals omega 
      tauto 
    · -- Assume q ≤ 2 
      interval_cases q <;> norm_num at hq ⊢ <;> tauto 
  have hr2 : r = 2 := by 
    rw [show q = 2 by omega] at h6 
    omega 
  omega