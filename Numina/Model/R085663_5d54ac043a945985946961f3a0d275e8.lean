import Mathlib

theorem inequalities_12671 :
    ∑ᶠ x ∈ {x : ℤ | 1 < abs (x - 2) ∧ abs (x - 2) < 4}, x = 8 := by

  have h1 : {x : ℤ | 1 < abs (x - 2) ∧ abs (x - 2) < 4} = {-1, 0, 4, 5} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Forward direction: If (1 < abs (x - 2) ∧ abs (x - 2) < 4) then x ∈ {-1, 0, 4, 5}
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : abs (x - 2) > 1 := by linarith
      have h4 : abs (x - 2) < 4 := by linarith
      by_cases h5 : x - 2 ≥ 0
      · -- Case 1: x - 2 ≥ 0, so abs (x - 2) = x - 2
        rw [abs_of_nonneg h5] at h3 h4
        omega
      · -- Case 2: x - 2 < 0, so abs (x - 2) = -(x - 2)
        rw [abs_of_neg (lt_of_not_ge h5)] at h3 h4
        omega
    · -- Backward direction: If x ∈ {-1, 0, 4, 5} then (1 < abs (x - 2) ∧ abs (x - 2) < 4)
      rintro (rfl | rfl | rfl | rfl)
      · -- x = -1
        constructor
        · norm_num [abs]
        · norm_num [abs]
      · -- x = 0
        constructor
        · norm_num [abs]
        · norm_num [abs]
      · -- x = 4
        constructor
        · norm_num [abs]
        · norm_num [abs]
      · -- x = 5
        constructor
        · norm_num [abs]
        · norm_num [abs]

  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> rfl
  <;> norm_num
  <;> try { omega }