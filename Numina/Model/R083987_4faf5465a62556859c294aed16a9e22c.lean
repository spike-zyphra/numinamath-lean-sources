import Mathlib

open Real
open scoped BigOperators

/- Given that the positive integer solutions of the inequality $3x-a\leqslant 0$ are exactly $1$, $2$, $3$, then the range of values for $a$ is ___          ___. -/
theorem inequalities_903 (a : ℕ) :
  {x : ℕ | 0 < x ∧ 3 * x - a ≤ 0} = {1, 2, 3} ↔ 9 ≤ a ∧ a < 12 := by
  constructor
  · -- Forward: if {x : ℕ | 0 < x ∧ 3 * x - a ≤ 0} = {1, 2, 3} then 9 ≤ a ∧ a < 12
    intro h
    have h1 : 3 ∈ {x : ℕ | 0 < x ∧ 3 * x - a ≤ 0} := by
      rw [h]
      simp
    rcases h1 with ⟨h2, h3⟩
    have h4 : a ≥ 9 := by 
      omega
      -- trivial inequality
    have h5 : 4 ∉ {x : ℕ | 0 < x ∧ 3 * x - a ≤ 0} := by
      rw [h]
      simp
    simp at h5
    have h6 : a < 12 := by 
      omega
    exact ⟨h4, h6⟩
  · -- Backward: if 9 ≤ a < 12, then {x : ℕ | 0 < x ∧ 3 * x - a ≤ 0} = {1, 2, 3}
    rintro ⟨h1, h2⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton
      ]
    constructor
    · -- Show {x | 0 < x ∧ 3 * x - a ≤ 0} ⊆ {1, 2, 3}
      intro h
      rcases h with ⟨hx1, hx2⟩
      have h3 : x ≤ 3 := by
        omega
      interval_cases x <;> omega
    · -- Show {1, 2, 3} ⊆ {x | 0 < x ∧ 3 * x - a ≤ 0}
      rintro (rfl | rfl | rfl)
      · constructor
        · norm_num
        · omega
      · constructor
        · norm_num
        · omega
      · constructor
        · norm_num
        · omega