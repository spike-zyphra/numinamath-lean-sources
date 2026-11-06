import Mathlib

theorem number_theory_178469 (p : ℕ) (hp : Nat.Prime p) :
    ∃ n u v : ℕ, n > 0 ∧ u > 0 ∧ v > 0 ∧
      (n.divisors.card = p ^ u) ∧
      (∑ d ∈ n.divisors, d) = p ^ v ↔ p = 2 := by 
  use 3, 1, 2
  constructor 
  · -- Forward direction: if the conditions hold, then p = 2
    intro h 
    rcases h with ⟨h1, h2, h3, hdiv, hsum⟩ 
    have h1 : (3 : ℕ).divisors.card = p ^ 1 := by 
      simpa using hdiv
    have h2 : ∑ d in (3 : ℕ).divisors, d = p ^ 2 := by 
      simpa using hsum
    have h3_eq : (3 : ℕ).divisors.card = 2 := by 
      native_decide 
    have hσ3_eq : (∑ d in (3 : ℕ).divisors, d) = 4 := by
      native_decide 
    have h1' : p ^ 1 = 2 := by
      rw [h3_eq] at h1
      nlinarith 
    have h1σ : p ^ 2 = 4 := by
      rw [hσ3_eq] at h2
      nlinarith 
    have h3' : p = 2 := by
      have : p ≤ 2 := by
        by_contra h
        push_neg at h 
        have h4 : p ^ 2 > 4 := by
          have h5 : p ≥ 3 := by
            omega 
          have h6 : p ^ 2 ≥ 3 ^ 2 := by 
            apply Nat.pow_le_pow_of_le_left 
            all_goals omega 
          nlinarith 
          all_goals nlinarith
        nlinarith 
      interval_cases p <;> norm_num at hp h1' h1σ <;> nlinarith 
    linarith 
  · -- Backward direction: if p = 2, the conditions hold 
    intro h 
    rw [h]
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    constructor 
    · -- Show that the number of divisors of 3 is 2^1 
      native_decide 
    · -- Show that the sum of the divisors of 3 is 2^2 
      native_decide