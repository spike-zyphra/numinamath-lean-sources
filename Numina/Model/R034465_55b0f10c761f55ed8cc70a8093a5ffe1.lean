import Mathlib

theorem number_theory_299773 (k : ℕ) (hk : k ≥ 2) :
    ∃ n : ℕ, n > 0 ∧ IsSquare ((∑ i ∈ Finset.range k, (n + i)^2) / k) ↔ k = 31 := by
  by_cases h : k = 31
  · -- Assume k = 31.
    rw [h]
    use 4
    constructor
    · -- Forward: show if n > 0 ∧ IsSquare ..., then k = 31
      intro h
      tauto
    · -- Backward: show k = 31 → (n > 0 ∧ IsSquare ...)
      intro h_eq
      constructor
      · -- Show n > 0.
        norm_num
      · -- Show IsSquare ...
        native_decide
  · -- Assume k ≠ 31.
    use 0
    simp at *
    all_goals try { tauto }