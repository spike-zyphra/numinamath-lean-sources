import Mathlib

theorem algebra_262519 (a : ℕ → ℤ) (ha : ∀ n, a n = 43 - 4 * n) :
    {n | 0 ≤ n ∧ n < 20 ∧ a n > 0}.encard = 11 := by
  have h1 : {n | 0 ≤ n ∧ n < 20 ∧ a n > 0} = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n is in the set
      rintro ⟨h0, h1, h2⟩
      have h3 : n < 20 := by linarith
      have h4 : a n > 0 := h2
      have h5 : 43 - 4 * (n : ℤ) > 0 := by
        rw [ha n] at h4
        linarith
      have h6 : n ≤ 10 := by
        by_contra h
        push_neg at h
        have h7 : (n : ℤ) ≥ 11 := by omega
        have h8 : 4 * (n : ℤ) ≥ 44 := by linarith [h7]
        have h9 : (43 - 4 * (n : ℤ) : ℤ) ≤ -1 := by linarith
        linarith
      interval_cases n <;> tauto
    · -- Assume n is in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 0
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show a 0 > 0
          rw [ha 0]
          norm_num
      · -- n = 1
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show a 1 > 0
          rw [ha 1]
          norm_num
      · -- n = 2
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show a 2 > 0
          rw [ha 2]
          norm_num
      · -- n = 3
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show a 3 > 0
          rw [ha 3]
          norm_num
      · -- n = 4
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show a 4 > 0
          rw [ha 4]
          norm_num
      · -- n = 5
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show a 5 > 0
          rw [ha 5]
          norm_num
      · -- n = 6
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show a 6 > 0
          rw [ha 6]
          norm_num
      · -- n = 7
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show a 7 > 0
          rw [ha 7]
          norm_num
      · -- n = 8
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show a 8 > 0
          rw [ha 8]
          norm_num
      · -- n = 9
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show a 9 > 0
          rw [ha 9]
          norm_num
      · -- n = 10
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show a 10 > 0
          rw [ha 10]
          norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { norm_num }