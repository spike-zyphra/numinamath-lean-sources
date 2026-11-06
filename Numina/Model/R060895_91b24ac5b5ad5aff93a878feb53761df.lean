import Mathlib

theorem inequalities_302303 :
    ∑ᶠ x ∈ {x : ℕ | |(2 * x : ℤ) - 1| < 6}, x = 6 := by 
  have h1 : {x : ℕ | |(2 * x : ℤ) - 1| < 6} = {0, 1, 2, 3} := by
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume that x is in left side
      intro h
      norm_num at h ⊢
      have h1 : x < 4 := by 
        by_cases h2 : (2 * x : ℤ) - 1 ≥ 0
        · -- Case 1: 2x - 1 ≥ 0, so |2x - 1| = 2x - 1
          have h3 : (2 * x : ℤ) - 1 < 6 := by 
            rw [abs_of_nonneg h2] at h
            linarith
          have h4 : (2 * x : ℤ) < 7 := by linarith
          have h5 : x < 4 := by 
            omega
          exact h5
        · -- Case 2: 2x - 1 < 0, so |2x - 1| = -(2x - 1)
          have h3 : -( (2 * x : ℤ) - 1 ) < 6 := by 
            rw [abs_of_neg (lt_of_not_ge h2)] at h
            linarith
          omega
      interval_cases x <;> tauto
    · -- Assume that x is in right side
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 0
        norm_num 
      · -- x = 1
        norm_num 
      · -- x = 2
        norm_num 
      · -- x = 3
        norm_num 
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> rfl
  <;> try { trivial }
  <;> try { omega }