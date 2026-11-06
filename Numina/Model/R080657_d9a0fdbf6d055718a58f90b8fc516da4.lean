import Mathlib

theorem algebra_21822 : {x : ℤ | abs x + 5 < 7 ∧ abs (x - 3) > 2}.ncard = 2 := by
  have h1 : {x : ℤ | abs x + 5 < 7 ∧ abs (x - 3) > 2} = {-1, 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x satisfies both conditions and prove x ∈ {-1, 0}
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : x ≥ -1 := by
        by_cases h' : x ≥ 0
        · -- If x ≥ 0, then abs x = x
          rw [abs_of_nonneg h'] at h1
          linarith
        · -- If x < 0, then abs x = -x
          rw [abs_of_neg (lt_of_not_ge h')] at h1
          linarith
      have h4 : x ≤ 1 := by
        by_cases h' : x ≥ 0
        · -- If x ≥ 0, then abs x = x
          rw [abs_of_nonneg h'] at h1
          linarith
        · -- If x < 0, then abs x = -x
          rw [abs_of_neg (lt_of_not_ge h')] at h1
          linarith
      interval_cases x <;> norm_num [abs] at h1 h2 ⊢ <;> tauto
    · -- Assume x ∈ {-1, 0} and prove it satisfies both conditions
      rintro (rfl | rfl)
      · -- x = -1
        norm_num [abs]
      · -- x = 0
        norm_num [abs]
  rw [h1]
  rw [Set.ncard_pair (by norm_num)]