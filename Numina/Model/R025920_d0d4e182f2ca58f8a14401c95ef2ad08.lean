import Mathlib

theorem number_theory_162134 (p : ℕ) (hp : Nat.Prime p) :
    ∃ a > 0, ∀ k : ℕ, ¬p ∣ k → k ^ a ≡ k ^ (p - 2) [MOD p] := by
  by_cases h : p > 2
  · -- Assume p > 2, we set a = p - 2 > 0.
    use p - 2
    constructor
    · -- Show a > 0
      omega
    intro k hk
    all_goals
      simp [Nat.ModEq]
  · -- Assume p ≤ 2, then p = 2.
    have hp2 : p = 2 := by
      by_cases hp2 : p > 2
      · linarith
      interval_cases p <;> norm_num at hp ⊢
    subst hp2
    use 1
    constructor
    · -- Show a > 0
      norm_num
    intro k hk
    have : k % 2 = 1 := by
      by_contra h
      push_neg at h
      have hdiv : (2 : ℕ) ∣ k := by
        omega
      omega
    simp [Nat.ModEq, Nat.pow_mod, this]