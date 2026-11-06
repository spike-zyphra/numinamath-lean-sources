import Mathlib

theorem algebra_140045 : {n | n ∈ Finset.range 5 ∧ (n = 0 → (20 / 100 : ℝ) * 40 = 8) ∧
    (n = 1 → 2^3 = 8) ∧ (n = 2 → 3^2 - 1^2 = 8) ∧ (n = 3 → 7 - 3 * 2 = 8) ∧
    (n = 4 → 2 * (6 - 4)^2 = 8)}.ncard = 4 := by
  have h1 : {n | n ∈ Finset.range 5 ∧ (n = 0 → (20 / 100 : ℝ) * 40 = 8) ∧
      (n = 1 → 2^3 = 8) ∧ (n = 2 → 3^2 - 1^2 = 8) ∧ (n = 3 → 7 - 3 * 2 = 8) ∧
      (n = 4 → 2 * (6 - 4)^2 = 8)} = {0, 1, 2, 4} := by
    ext n
    simp only [Finset.mem_range, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Forward direction: if n is in the left set, it's in the right
      intro h
      rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
      interval_cases n <;> norm_num at h2 h3 h4 h5 h6 <;> tauto
    · -- Backward direction: if n is in the right set, it's in the left
      intro h
      rcases h with (rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }