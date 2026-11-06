import Mathlib

theorem algebra_328060 :
    {p : ℕ | p = 1 ∧ ∃ x : ℝ, x^3 + 3 * x^2 - 4 = (x + 2) * (x^2 + x - 2)}.encard = 1 := by 
  have h1 : {p : ℕ | p = 1 ∧ ∃ x : ℝ, x^3 + 3 * x^2 - 4 = (x + 2) * (x^2 + x - 2)} = {1} := by 
    ext p 
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor 
    · intro h 
      exact h.1 
    · intro hp 
      refine ⟨hp, 0, by norm_num⟩
  rw [h1] 
  simp