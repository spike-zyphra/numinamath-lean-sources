import Mathlib

theorem number_theory_154232 (p : ℕ) (hp : p.Prime) (hne : p ≠ 3) :
    ¬(∃ q : ℕ, q.Prime ∧ q = 14 * p ^ 2 + 1) := by 
  rintro ⟨q, ⟨hq, hq_eq⟩⟩ 
  have h1 : p % 3 = 1 ∨ p % 3 = 2 := by 
    by_cases h3 : p > 3
    · -- Case p > 3
      by_contra h 
      push_neg at h 
      have h2 : p % 3 = 0 := by 
        omega 
      have h3 : ¬p.Prime := by 
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
        all_goals omega 
      contradiction
    · -- Case p ≤ 3
      have h4 : p ≤ 3 := by omega 
      interval_cases p <;> norm_num at hp hne 
      <;> omega 
  have h2 : q % 3 = 0 := by 
    have h11 : p % 3 = 1 ∨ p % 3 = 2 := h1 
    have h12 : p ^ 2 % 3 = 1 := by 
      rcases h11 with (h | h)
      · 
        simp [Nat.pow_mod, h]
      · 
        simp [Nat.pow_mod, h]
    have h13 : (14 * p ^ 2 + 1) % 3 = 0 := by 
      omega 
    omega 
  have h3' : q > 3 := by 
    rw [hq_eq] 
    have h1 : p > 1 := by 
      by_contra h 
      push_neg at h 
      interval_cases p <;> norm_num at hp hne 
    nlinarith [show p ≥ 2 by omega, show p ^ 2 ≥ 4 by nlinarith] 
  have h4 : q % 3 = 0 := h2 
  have h5 : q > 3 := h3' 
  have h6 : ¬q.Prime := by 
    apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ q by omega)
    all_goals omega 
  contradiction