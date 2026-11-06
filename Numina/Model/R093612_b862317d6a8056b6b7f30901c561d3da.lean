import Mathlib

open Real
open scoped BigOperators

theorem inequalities_4803 : Set.ncard {x : ℤ | 0 < x ∧ -5 ≤ (9 * x + 3) / 4 ∧ (9 * x + 3) / 4 ≤ 29} = 12 := by
  have h1 : {x : ℤ | 0 < x ∧ -5 ≤ (9 * x + 3) / 4 ∧ (9 * x + 3) / 4 ≤ 29} = Set.Icc 1 12 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Show that if x satisfies the conditions, then 1 ≤ x ≤ 12
      rintro ⟨h1, h2, h3⟩
      omega
    · -- Show that if 1 ≤ x ≤ 12, then x satisfies the conditions
      rintro ⟨h1, h2⟩
      constructor
      · linarith
      constructor
      · omega
      · omega
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try native_decide