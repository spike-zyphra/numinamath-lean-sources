import Mathlib

theorem number_theory_304150 (k : ℤ) :
    ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ (b + 1 : ℝ) / a + (a + 1 : ℝ) / b = k ↔ k = 3 ∨ k = 4 := by 
  by_cases h1 : k = 3
  · -- Assume k = 3, we can choose a = 2, b = 2.
    use 2, 2
    constructor
    · -- Assume a = 2, b = 2 satisfy the equation
      intro h
      rcases h with ⟨ha, hb, heq⟩
      rw [show (k : ℝ) = (3 : ℝ) by exact_mod_cast h1] at heq
      norm_num at heq ⊢
      <;> tauto
    · -- Show that k = 3 ∨ k = 4 implies the equation
      rintro (h | h)
      · -- Case k = 3
        rw [show (k : ℝ) = (3 : ℝ) by exact_mod_cast h1]
        norm_num at *
      · -- Case k = 4, which contradicts k = 3
        exfalso
        omega
  by_cases h2 : k = 4
  · -- Assume k = 4, we can choose a = 1, b = 1.
    use 1, 1
    constructor
    · -- Assume a = 1, b = 1 satisfy the equation
      intro h
      rcases h with ⟨ha, hb, heq⟩
      rw [show (k : ℝ) = (4 : ℝ) by exact_mod_cast h2] at heq
      norm_num at heq ⊢
      <;> tauto
    · -- Show that k = 3 ∨ k = 4 implies the equation
      rintro (h | h)
      · -- Case k = 3, which contradicts k = 4
        exfalso
        omega
      · -- Case k = 4
        rw [show (k : ℝ) = (4 : ℝ) by exact_mod_cast h2]
        norm_num at *
  · -- k ≠ 3 and k ≠ 4
    push_neg at h1 h2
    use 0, 0
    simp at *
    all_goals
      omega