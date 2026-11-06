import Mathlib

theorem number_theory_82222 (p : ℕ) (hp : Nat.Prime p) :
    ∃ q r : ℕ, 0 < q ∧ 0 < r ∧ ¬p ∣ q ∧ ¬3 ∣ q ∧ p^3 = r^3 - q^2 ↔ p = 7 := by 
  use 13 
  use 8 
  constructor
  · -- Forward direction: if the conditions hold, then p = 7
    intro h
    rcases h with ⟨h1, h2, h3, h4, eq⟩
    have hp3 : p^3 = 343 := by
      omega -- This solves the arithmetic goal to compute p^3 from the equation
    have h_eq : p = 7 := by
      have h1 : p^3 = 343 := hp3
      have h2 : p ≤ 7 := by
        by_contra h
        push_neg at h
        have h3 : p ≥ 8 := by omega
        have h4 : p^3 ≥ 8^3 := by
          apply Nat.pow_le_pow_of_le_left h3 3
        norm_num at h4 h1
        all_goals nlinarith
      interval_cases p <;> try { tauto }
      <;> norm_num at h1 <;> tauto
    exact h_eq
  · -- Backward direction: if p = 7, then the conditions hold
    intro h_eq
    rw [h_eq]
    constructor
    · norm_num -- 0 < q
    constructor
    · norm_num -- 0 < r
    constructor
    · norm_num -- ¬p ∣ q
    constructor
    · norm_num -- ¬3 ∣ q
    · norm_num -- p^3 = r^3 - q^2