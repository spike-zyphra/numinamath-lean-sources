import Mathlib

theorem algebra_233018 (p : ℕ) (hp : p > 0) :
    ∃ k : ℕ, 0 < k ∧ k = (3 * p + 25) / (2 * p - 5) ↔
    (3 ≤ p ∧ p ≤ 35) := by 
  by_cases h1 : 3 ≤ p ∧ p ≤ 35
  · -- Assume (3 ≤ p ∧ p ≤ 35)
    use (3 * p + 25) / (2 * p - 5)
    have h4 : 2 * p - 5 ≥ 1 := by 
      omega
    have h5 : (3 * p + 25) / (2 * p - 5) > 0 := by
      have h7 : 3 * p + 25 ≥ 34 := by 
        omega
      have h8 : 2 * p - 5 ≥ 1 := by 
        omega
      apply Nat.div_pos
      all_goals 
        omega
    constructor
    · -- Forward direction: (k > 0 ∧ k = ... ) → (3 ≤ p ∧ p ≤ 35)
      intro h
      tauto
    · -- Backward direction: (3 ≤ p ∧ p ≤ 35) → (k > 0 ∧ k = ... )
      intro h
      constructor
      · -- k > 0
        exact h5
      · -- k = (3 * p + 25) / (2 * p - 5)
        rfl
  · -- Assume ¬ (3 ≤ p ∧ p ≤ 35)
    use 0
    simp at h1 ⊢
    all_goals 
      omega