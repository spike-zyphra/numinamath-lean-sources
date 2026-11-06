import Mathlib

theorem number_theory_251614: {n: ℤ | 0 ≤ n ∧ ∃ x y: ℤ, (0 ≤ x ∧ 0 ≤ y ∧ x + y = n ^ 2 ∧ 10 * x + y = n ^ 3)}
  = {0, 1, 3, 6 ,9, 10} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume n in left side, prove n in right side
    intro h
    rcases h with ⟨hn, x, y, hx, hy, h1, h2⟩
    have h3 : 9 * x = n ^ 3 - n ^ 2 := by
      omega
    have h4 : n ^ 3 - n ^ 2 ≥ 0 := by
      nlinarith [sq_nonneg (n : ℤ)]
    have h5 : n ≤ 10 := by
      nlinarith [sq_nonneg (n - 0 : ℤ), sq_nonneg (n - 1 : ℤ), sq_nonneg (n - 3 : ℤ), sq_nonneg (n - 6 : ℤ), sq_nonneg (n - 9 : ℤ), sq_nonneg (n - 10 : ℤ)]
    have h6 : n ≥ 0 := hn
    interval_cases n <;> omega
  · -- Show that if n ∈ {0, 1, 3, 6, 9, 10}, then there exists x, y.
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · -- n = 0
      constructor
      · norm_num
      · -- Show existence of x, y
        use 0, 0
        all_goals norm_num
    · -- n = 1
      constructor
      · norm_num
      · -- Show existence of x, y
        use 0, 1
        all_goals norm_num
    · -- n = 3
      constructor
      · norm_num
      · -- Show existence of x, y
        use 2, 7
        all_goals norm_num
    · -- n = 6
      constructor
      · norm_num
      · -- Show existence of x, y
        use 20, 16
        all_goals norm_num
    · -- n = 9
      constructor
      · norm_num
      · -- Show existence of x, y
        use 72, 9
        all_goals norm_num
    · -- n = 10
      constructor
      · norm_num
      · -- Show existence of x, y
        use 100, 0
        all_goals norm_num