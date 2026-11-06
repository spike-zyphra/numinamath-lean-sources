import Mathlib

theorem algebra_15015 :
    Set.ncard {n : ℤ | -50 < n ^ 3 ∧ n ^ 3 < 50} = 7 := by
  have h1 : {n : ℤ | -50 < n ^ 3 ∧ n ^ 3 < 50} = {-3, -2, -1, 0, 1, 2, 3} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n is in the set {n : ℤ | -50 < n^3 ∧ n^3 < 50}
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : n ≥ -3 := by
        by_contra h4
        push_neg at h4
        have h5 : n ≤ -4 := by omega
        nlinarith [sq_nonneg (n + 4), sq_nonneg (n - 3), sq_nonneg (n + 2), sq_nonneg (n - 1)]
      have h4 : n ≤ 3 := by
        by_contra h5
        push_neg at h5
        have h6 : n ≥ 4 := by omega
        nlinarith [sq_nonneg (n - 4), sq_nonneg (n + 4), sq_nonneg (n - 3), sq_nonneg (n + 2)]
      interval_cases n <;> tauto
    · -- Assume n ∈ {-3, -2, -1, 0, 1, 2, 3}; we need to prove -50 < n^3 ∧ n^3 < 50
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor <;> norm_num
      · constructor <;> norm_num
      · constructor <;> norm_num
      · constructor <;> norm_num
      · constructor <;> norm_num
      · constructor <;> norm_num
      · constructor <;> norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }