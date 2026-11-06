import Mathlib

open Real
open scoped BigOperators

/- The sum of all integer solutions to the system of inequalities $\begin{cases}x-4\leqslant 8-2x \\ x>-\dfrac{2}{3} \end{cases}$ is ___          ___. -/
theorem inequalities_2300 :
  ∑ᶠ x ∈ {x : ℤ | x - 4 ≤ 8 - 2 * x ∧ x > -2 / 3}, x = 10 := by
  have h1 : {x : ℤ | x - 4 ≤ 8 - 2 * x ∧ x > -2 / 3} = {0, 1, 2, 3, 4} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x satisfies both inequalities
      rintro ⟨h1, h2⟩
      omega
    · -- Assume x in {0, 1, 2, 3, 4}
      rintro (rfl | rfl | rfl | rfl | rfl)
      all_goals
        constructor <;> omega
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> rfl