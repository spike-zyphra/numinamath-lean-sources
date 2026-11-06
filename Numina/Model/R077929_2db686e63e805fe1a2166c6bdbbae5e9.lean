import Mathlib

theorem algebra_94971 : Set.ncard {x : ℤ | x^4 - 51 * x^2 + 50 < 0} = 12 := by
  have h1 : {x : ℤ | x^4 - 51 * x^2 + 50 < 0} = {-7, -6, -5, -4, -3, -2, 2, 3, 4, 5, 6, 7} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
      Set.union_singleton]
    constructor
    · -- First, we show that if n^4 - 51n^2 + 50 < 0, then n ∈ {-7, -6, -5, -4, -3, -2, 2, 3, 4, 5, 6, 7}
      intro h
      have h2 : n^4 - 51 * n^2 + 50 < 0 := by nlinarith
      have h3 : n ≥ -7 := by nlinarith [sq_nonneg (n + 7), sq_nonneg (n - 7), sq_nonneg (n + 6), sq_nonneg (n - 6), sq_nonneg (n + 5), sq_nonneg (n - 5), sq_nonneg (n + 4), sq_nonneg (n - 4), sq_nonneg (n + 3), sq_nonneg (n - 3), sq_nonneg (n + 2), sq_nonneg (n - 2)]
      have h4 : n ≤ 7 := by nlinarith [sq_nonneg (n + 7), sq_nonneg (n - 7), sq_nonneg (n + 6), sq_nonneg (n - 6), sq_nonneg (n + 5), sq_nonneg (n - 5), sq_nonneg (n + 4), sq_nonneg (n - 4), sq_nonneg (n + 3), sq_nonneg (n - 3), sq_nonneg (n + 2), sq_nonneg (n - 2)]
      interval_cases n <;> tauto
    · -- Now, we show that if n ∈ {-7, -6, -5, -4, -3, -2, 2, 3, 4, 5, 6, 7}, then n^4 - 51n^2 + 50 < 0
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try native_decide