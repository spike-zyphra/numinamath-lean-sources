import Mathlib

open Real Set

theorem algebra_112992 :
    {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n^2 = 123 - sqrt x}.ncard = 12 := by
  have h1 : {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n^2 = 123 - sqrt x} = {15129, 14884, 14161, 12996, 11449, 9604, 7569, 5476, 3481, 1764, 529, 4} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x in the left side, prove x in the right side
      rintro ⟨n, hx1, heq⟩
      have heq2 : (n : ℝ) ^ 2 = (123 : ℝ) - Real.sqrt x := by
        exact_mod_cast (show (n ^ 2 : ℝ) = (123 - Real.sqrt x : ℝ) by exact_mod_cast heq)
      have h2 : n ^ 2 ≤ 123 := by
        by_contra h
        push_neg at h
        have heq3 : (n : ℝ) ^ 2 > (123 : ℝ) := by
          exact_mod_cast (show (n ^ 2 : ℝ) > (123 : ℝ) by exact_mod_cast h)
        have h3 : Real.sqrt x < 0 := by
          nlinarith [Real.sqrt_nonneg x]
        have h4 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
        linarith
      have h9 : n ≤ 11 := by
        by_contra h
        push_neg at h
        have h10 : n ≥ 12 := by omega
        have h11 : n ^ 2 ≥ 144 := by
          nlinarith [h10, sq_nonneg (n : ℕ)]
        have h12 : n ^ 2 > 123 := by
          nlinarith
        exfalso
        have heq3 : (n : ℝ) ^ 2 > (123 : ℝ) := by
          exact_mod_cast (show (n ^ 2 : ℝ) > (123 : ℝ) by exact_mod_cast h12)
        have h3 : Real.sqrt x < 0 := by
          nlinarith [Real.sqrt_nonneg x]
        have h4 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
        linarith
      have heq3 : (Real.sqrt x) = (123 - (n : ℝ) ^ 2 : ℝ) := by
        nlinarith
      have heq4 : x = ((Real.sqrt x) : ℝ) ^ 2 := by
        rw [Real.sq_sqrt]
        have hx2 : (0 : ℝ) ≤ x := by linarith
        linarith
      have heq5 : x = ((123 - (n : ℝ) ^ 2 : ℝ) : ℝ) ^ 2 := by
        rw [heq4, heq3]
      have h10 : n ≤ 11 := h9
      have heq7 : x = ((123 - (n : ℝ) ^ 2 : ℝ) : ℝ) ^ 2 := by
        linarith
      have heq8 : n ≤ 11 := h9
      interval_cases n <;> norm_num at heq7 heq2 heq3 hx1 heq heq5
      <;> norm_num [heq7]
    · -- Assume x in the right side, prove x in the left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 15129
        use 0
        constructor
        · norm_num
        ·
          have h4 : Real.sqrt (15129 : ℝ) = (123 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h4]
          norm_num
      · -- x = 14884
        use 1
        constructor
        · norm_num
        ·
          have h4 : Real.sqrt (14884 : ℝ) = (122 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h4]
          norm_num
      · -- x = 14161
        use 2
        constructor
        · norm_num
        ·
          have h4 : Real.sqrt (14161 : ℝ) = (119 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h4]
          norm_num
      · -- x = 12996
        use 3
        constructor
        · norm_num
        ·
          have h4 : Real.sqrt (12996 : ℝ) = (114 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h4]
          norm_num
      · -- x = 11449
        use 4
        constructor
        · norm_num
        ·
          have h4 : Real.sqrt (11449 : ℝ) = (107 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h4]
          norm_num
      · -- x = 9604
        use 5
        constructor
        · norm_num
        ·
          have h4 : Real.sqrt (9604 : ℝ) = (98 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h4]
          norm_num
      · -- x = 7569
        use 6
        constructor
        · norm_num
        ·
          have h4 : Real.sqrt (7569 : ℝ) = (87 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h4]
          norm_num
      · -- x = 5476
        use 7
        constructor
        · norm_num
        ·
          have h4 : Real.sqrt (5476 : ℝ) = (74 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h4]
          norm_num
      · -- x = 3481
        use 8
        constructor
        · norm_num
        ·
          have h4 : Real.sqrt (3481 : ℝ) = (59 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h4]
          norm_num
      · -- x = 1764
        use 9
        constructor
        · norm_num
        ·
          have h4 : Real.sqrt (1764 : ℝ) = (42 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h4]
          norm_num
      · -- x = 529
        use 10
        constructor
        · norm_num
        ·
          have h4 : Real.sqrt (529 : ℝ) = (23 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h4]
          norm_num
      · -- x = 4
        use 11
        constructor
        · norm_num
        ·
          have h4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h4]
          norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]