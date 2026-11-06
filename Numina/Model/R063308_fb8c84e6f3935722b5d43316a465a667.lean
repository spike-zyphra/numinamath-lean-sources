import Mathlib

theorem inequalities_6480 : {x : ℤ | -3 ≤ ((x - 7) * 2 + 5) / 3 ∧ ((x - 7) * 2 + 5) / 3 < 5}.ncard = 12 := by
  have h1 : {x : ℤ | -3 ≤ ((x - 7) * 2 + 5) / 3 ∧ ((x - 7) * 2 + 5) / 3 < 5} = Set.Icc 0 11 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume x satisfies the inequality, we need to show 0 ≤ x ≤ 11
      rintro ⟨h1, h2⟩
      omega
    · -- Assume 0 ≤ x ≤ 11, we need to show the inequality holds
      rintro ⟨h1, h2⟩
      omega
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide