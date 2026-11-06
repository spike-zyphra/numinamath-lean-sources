import Mathlib


theorem algebra_96075 : {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n^2 = 120 - Real.sqrt x}.ncard = 11 := by
  have h1 : {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n^2 = 120 - Real.sqrt x} = {14400, 14161, 13456, 12321, 10816, 9025, 7056, 5041, 3136, 1521, 400} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x in left side, prove in right side
      rintro ⟨n, hx_nonneg, heq⟩
      have h1 : (Real.sqrt x) ≥ 0 := by positivity
      have h2 : (n : ℝ) ^ 2 = 120 - Real.sqrt x := by exact_mod_cast heq
      have h3 : (n : ℝ) ^ 2 ≤ 120 := by
        nlinarith [h1]
      have h4 : n ≤ 10 := by
        by_contra h
        push_neg at h
        have h5 : n ≥ 11 := by
          omega
        have h6 : (n : ℝ) ≥ (11 : ℝ) := by exact_mod_cast h5
        nlinarith
      have h7 : x = ((120 - (n : ℝ) ^ 2) )^2 := by
        have h8 : Real.sqrt x = 120 - (n : ℝ) ^ 2 := by
          nlinarith
        have h9 : Real.sqrt x ≥ 0 := by positivity
        have h10 : x = (Real.sqrt x) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        rw [h8] at h10
        nlinarith
      have : x = (14400 : ℝ) ∨ x = (14161 : ℝ) ∨ x = (13456 : ℝ) ∨ x = (12321 : ℝ) ∨ x = (10816 : ℝ) ∨ x = (9025 : ℝ) ∨ x = (7056 : ℝ) ∨ x = (5041 : ℝ) ∨ x = (3136 : ℝ) ∨ x = (1521 : ℝ) ∨ x = (400 : ℝ) := by
        have h8 : n ≤ 10 := h4
        have h9 : n ≥ 0 := by omega
        interval_cases n <;> norm_num at h7 ⊢
        <;> tauto
      tauto
    · -- Assume x in right side, prove in left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 14400
        use 0
        constructor
        · norm_num
        ·
          have h11 : Real.sqrt (14400 : ℝ) = 120 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h11]
          norm_num
      · -- x = 14161
        use 1
        constructor
        · norm_num
        ·
          have h11 : Real.sqrt (14161 : ℝ) = 119 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h11]
          norm_num
      · -- x = 13456
        use 2
        constructor
        · norm_num
        ·
          have h11 : Real.sqrt (13456 : ℝ) = 116 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h11]
          norm_num
      · -- x = 12321
        use 3
        constructor
        · norm_num
        ·
          have h11 : Real.sqrt (12321 : ℝ) = 111 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h11]
          norm_num
      · -- x = 10816
        use 4
        constructor
        · norm_num
        ·
          have h11 : Real.sqrt (10816 : ℝ) = 104 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h11]
          norm_num
      · -- x = 9025
        use 5
        constructor
        · norm_num
        ·
          have h11 : Real.sqrt (9025 : ℝ) = 95 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h11]
          norm_num
      · -- x = 7056
        use 6
        constructor
        · norm_num
        ·
          have h11 : Real.sqrt (7056 : ℝ) = 84 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h11]
          norm_num
      · -- x = 5041
        use 7
        constructor
        · norm_num
        ·
          have h11 : Real.sqrt (5041 : ℝ) = 71 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h11]
          norm_num
      · -- x = 3136
        use 8
        constructor
        · norm_num
        ·
          have h11 : Real.sqrt (3136 : ℝ) = 56 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h11]
          norm_num
      · -- x = 1521
        use 9
        constructor
        · norm_num
        ·
          have h11 : Real.sqrt (1521 : ℝ) = 39 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h11]
          norm_num
      · -- x = 400
        use 10
        constructor
        · norm_num
        ·
          have h11 : Real.sqrt (400 : ℝ) = 20 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h11]
          norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  norm_num