import Mathlib

theorem algebra_12002 (f : ℝ → ℝ) (hf : f = fun y => -2 * y ^ 2 + y + 1) :
    Set.ncard {x | ∃ y, x = f y ∧ y = 0} = 1 := by 
  have h1 : {x | ∃ y, x = f y ∧ y = 0} = {1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume x ∈ {x | ∃ y, x = f y ∧ y = 0}, prove x ∈ {1}
      rintro ⟨y, rfl, rfl⟩
      simp [hf]
      <;> norm_num
    · -- Assume x ∈ {1}, prove x ∈ {x | ∃ y, x = f y ∧ y = 0}
      intro hx
      rw [hx]
      use 0
      all_goals simp [hf]
      <;> norm_num
  rw [h1]
  norm_num