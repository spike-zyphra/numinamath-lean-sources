import Mathlib

open Real
open scoped BigOperators

/- The sum of all integer solutions to the inequality $\left| x-1 \right|+\left| x-2 \right|\leqslant 3$ with respect to $x$ is ___          ___. -/
theorem inequalities_1349 :
  ∑ᶠ x ∈ {x : ℤ | abs (x - 1) + abs (x - 2) ≤ 3}, x = 6 := by
  have h1 : {x : ℤ | abs (x - 1) + abs (x - 2) ≤ 3} = {0, 1, 2, 3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First, prove if abs (x - 1) + abs (x - 2) ≤ 3, then x ∈ {0, 1, 2, 3}
      intro h
      have h2 : x ≥ 0 := by
        by_contra h2
        push_neg at h2
        have h3 : x < 0 := h2
        have h4 : x ≤ -1 := by omega
        have h5 : abs (x - 1) = 1 - x := by
          rw [abs_of_nonpos (by omega : x - 1 ≤ 0)]
          all_goals omega
        have h6 : abs (x - 2) = 2 - x := by
          rw [abs_of_nonpos (by omega : x - 2 ≤ 0)]
          all_goals omega
        rw [h5, h6] at h
        omega
      have h3 : x ≤ 3 := by
        by_contra h3
        push_neg at h3
        have h4 : x ≥ 4 := by omega
        have h7 : abs (x - 1) = x - 1 := by
          rw [abs_of_nonneg (by omega : x - 1 ≥ 0)]
        have h8 : abs (x - 2) = x - 2 := by
          rw [abs_of_nonneg (by omega : x - 2 ≥ 0)]
        rw [h7, h8] at h
        omega
      interval_cases x <;> tauto
    · -- Now the reverse: if x ∈ {0, 1, 2, 3}, then abs (x - 1) + abs (x - 2) ≤ 3
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 0
        norm_num [abs]
      · -- x = 1
        norm_num [abs]
      · -- x = 2
        norm_num [abs]
      · -- x = 3
        norm_num [abs]
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> try { native_decide }