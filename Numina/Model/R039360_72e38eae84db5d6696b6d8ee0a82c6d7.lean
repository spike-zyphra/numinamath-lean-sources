import Mathlib

theorem algebra_246263 :
    {d : ℝ | ∃ t : ℝ, d = 1.1 * t ∧ d = 0.7 * (t + 18)} = 
    {34.65} := by
  ext d
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: If d is in the left side, it's in the right side ( uniqueness )
    rintro ⟨t, h_eq1, h_eq2⟩
    have eq1 : d = 34.65 := by 
      norm_num at h_eq1 h_eq2
      linarith
    linarith
  · -- Second direction: If d is in the right side, it's in the left side ( existence )
    intro h_eq
    rw [h_eq]
    refine ⟨31.5, by norm_num, by norm_num⟩