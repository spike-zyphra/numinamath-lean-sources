import Mathlib

/-The number of integer pairs (m, n) that satisfy
1998 ^ 2 + m ^ 2 = 1997 ^ 2 + n ^ 2 ∧ 0 < m ∧ m < n ∧ n < 1998 is -/

theorem number_theory_304640: {(m, n): ℤ × ℤ |
  1998 ^ 2 + m ^ 2 = 1997 ^ 2 + n ^ 2 ∧ 0 < m ∧ m < n ∧ n < 1998}.encard = 3 := by

  -- we directly compute the set
  have h_eq: {(m, n): ℤ × ℤ |
  1998 ^ 2 + m ^ 2 = 1997 ^ 2 + n ^ 2 ∧ 0 < m ∧ m < n ∧ n < 1998} = {(397, 402), (109, 126), (19, 66)} := by
    ext ⟨m, n⟩
    constructor
    -- the forward direction
    .
      intro h
      simp only [Set.mem_setOf_eq] at h
      simp
      rcases h with ⟨h, lm, l, ln⟩

      -- we factorial at h
      replace h: (n - m) * (n + m) = 5 * 17 * 47 := by
        nlinarith
      norm_num at h

      -- hence n - m is a divisor of 5 * 17 * 47
      have d: n - m ∣ 3995 := by
        rw [← h]
        simp
      replace d: (n - m).natAbs ∈ Nat.divisors 3995 := by
        simp
        zify
        rw [show |n - m| = n - m by apply abs_of_nonneg; linarith]
        exact d
      have eq: Nat.divisors 3995 = {1, 5, 17, 47, 85, 235, 799, 3995} := by
        native_decide
      rw [eq] at d
      clear eq
      have o: n - m < 64 := by nlinarith
      simp at d
      zify at d
      rw [show |n - m| = n - m by apply abs_of_nonneg; linarith] at d
      rcases d with d | d | d | d | d | d | d | d
      all_goals simp [d] at o
      all_goals simp [d] at h; omega


    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h | h
      all_goals simp [h]


  -- then we count the cardinality
  rw [h_eq]
  simp [Set.encard_insert_of_not_mem]
  norm_num