import Mathlib

theorem number_theory_272968 : {x : ℤ | x > (5 / 7 : ℝ) ∧ x < (28 / 3 : ℝ)}.encard = 9 := by
  have h1 : {x : ℤ | x > (5 / 7 : ℝ) ∧ x < (28 / 3 : ℝ)} = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x is in {x : ℤ | x > (5 / 7 : ℝ) ∧ x < (28 / 3 : ℝ)}, we need to prove x ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9}
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : x ≥ 1 := by
        by_contra h
        push_neg at h
        have h4 : x ≤ 0 := by omega
        have h5 : (x : ℝ) ≤ (0 : ℝ) := by
          exact_mod_cast h4
        nlinarith
      have h4 : x ≤ 9 := by
        by_contra h
        push_neg at h
        have h5 : x ≥ 10 := by omega
        have h6 : (x : ℝ) ≥ (10 : ℝ) := by
          exact_mod_cast h5
        nlinarith
      interval_cases x <;> norm_num at *
    · -- Assume x ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9}, prove x ∈ {x : ℤ | x > (5 / 7 : ℝ) ∧ x < (28 / 3 : ℝ)}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 1
        constructor
        · norm_num
        · norm_num
      · -- x = 2
        constructor
        · norm_num
        · norm_num
      · -- x = 3
        constructor
        · norm_num
        · norm_num
      · -- x = 4
        constructor
        · norm_num
        · norm_num
      · -- x = 5
        constructor
        · norm_num
        · norm_num
      · -- x = 6
        constructor
        · norm_num
        · norm_num
      · -- x = 7
        constructor
        · norm_num
        · norm_num
      · -- x = 8
        constructor
        · norm_num
        · norm_num
      · -- x = 9
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }