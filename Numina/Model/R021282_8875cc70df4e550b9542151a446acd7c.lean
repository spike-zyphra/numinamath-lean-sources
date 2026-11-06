import Mathlib

theorem number_theory_251123 (a : ℕ) (ha : 2 ≤ a) :
    ∃ b ∈ Set.Icc 1 a, ∃ C : Set ℕ, C = {x | ∃ m n, x = a ^ m ∧ x = (a + 1) * n + b} ∧ C ≠ ∅ := by 
  use 1
  constructor
  · -- Show that 1 is in the interval [1, a].
    have h1 : 1 ≤ 1 := by linarith
    have h2 : 1 ≤ a := by linarith
    exact ⟨h1, h2⟩
  · -- Show that the set C is non-empty.
    use {x | ∃ m n, x = a ^ m ∧ x = (a + 1) * n + 1}
    constructor
    · -- Show the equality of the sets.
      rfl
    · -- Show that the set C is not empty.
      have h1_in_C : 1 ∈ {x | ∃ m n, x = a ^ m ∧ x = (a + 1) * n + 1} := by
        use 0, 0
        simp
      intro h
      have h1 : {x | ∃ m n, x = a ^ m ∧ x = (a + 1) * n + 1} = ∅ := by
        exact_mod_cast h
      have h2 : 1 ∈ {x | ∃ m n, x = a ^ m ∧ x = (a + 1) * n + 1} := h1_in_C
      rw [h1] at h2
      simp at h2
      all_goals linarith