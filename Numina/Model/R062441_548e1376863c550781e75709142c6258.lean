import Mathlib

theorem number_theory_319155 (A : ℕ → Set ℕ)
    (hA : ∀ n, A n = {x | 2 ^ n < x ∧ x < 2 ^ (n + 1) ∧ ∃ m, x = 7 * m + 1}) :
    ∑ᶠ x ∈ A 6, x = 891 := by
  have h1 : A 6 = {x | 64 < x ∧ x < 128 ∧ ∃ m, x = 7 * m + 1} := by
    rw [hA]
    norm_num
  rw [h1]
  have h2 : {x | 64 < x ∧ x < 128 ∧ ∃ m, x = 7 * m + 1} = {71, 78, 85, 92, 99, 106, 113, 120, 127} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x is in {x | 64 < x ∧ x < 128 ∧ ∃ m, x = 7 * m + 1}
      intro h
      rcases h with ⟨h1, h2, ⟨m, hm⟩⟩
      have h3 : m ≥ 10 := by
        omega
      have h4 : m ≤ 18 := by
        omega
      interval_cases m <;> norm_num [hm] at *
      <;> omega
    · -- Assume x is in {71, 78, 85, 92, 99, 106, 113, 120, 127}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 71
        constructor
        · norm_num
        constructor
        · norm_num
        · use 10
          all_goals norm_num
      · -- x = 78
        constructor
        · norm_num
        constructor
        · norm_num
        · use 11
          all_goals norm_num
      · -- x = 85
        constructor
        · norm_num
        constructor
        · norm_num
        · use 12
          all_goals norm_num
      · -- x = 92
        constructor
        · norm_num
        constructor
        · norm_num
        · use 13
          all_goals norm_num
      · -- x = 99
        constructor
        · norm_num
        constructor
        · norm_num
        · use 14
          all_goals norm_num
      · -- x = 106
        constructor
        · norm_num
        constructor
        · norm_num
        · use 15
          all_goals norm_num
      · -- x = 113
        constructor
        · norm_num
        constructor
        · norm_num
        · use 16
          all_goals norm_num
      · -- x = 120
        constructor
        · norm_num
        constructor
        · norm_num
        · use 17
          all_goals norm_num
      · -- x = 127
        constructor
        · norm_num
        constructor
        · norm_num
        · use 18
          all_goals norm_num
  rw [h2]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> rfl
  <;> try { norm_num }
  <;> try { rfl }
  <;> try { norm_num }