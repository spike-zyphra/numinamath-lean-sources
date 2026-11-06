import Mathlib

theorem inequalities_253801 : {x : ℤ | -5 < x - 1 ∧ x - 1 ≤ 5}.encard = 10 := by

  have h1 : {x : ℤ | -5 < x - 1 ∧ x - 1 ≤ 5} = {-3, -2, -1, 0, 1, 2, 3, 4, 5, 6} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      and_imp]
    constructor
    · -- Assume (x : ℤ) satisfies (✝ : -5 < x - 1 ∧ x - 1 ≤ 5)
      intro h
      rcases h with ⟨h1, h2⟩
      omega
    · -- Assume x ∈ (-3, -2, -1, 0, 1, 2, 3, 4, 5, 6)
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Let's verify it with x = -3
        constructor <;> omega
      · -- Let's verify it with x = -2
        constructor <;> omega
      · -- Let's verify it with x = -1
        constructor <;> omega
      · -- Let's verify it with x = 0
        constructor <;> omega
      · -- Let's verify it with x = 1
        constructor <;> omega
      · -- Let's verify it with x = 2
        constructor <;> omega
      · -- Let's verify it with x = 3
        constructor <;> omega
      · -- Let's verify it with x = 4
        constructor <;> omega
      · -- Let's verify it with x = 5
        constructor <;> omega
      · -- Let's verify it with x = 6
        constructor <;> omega
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try trivial