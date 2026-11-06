import Mathlib

set_option maxHeartbeats 0

theorem algebra_21618 :
  Set.encard {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n^2 = 63 - Real.sqrt x} = 8 := by
  have h1 : {x : ℝ | ∃ n : ℕ, 0 ≤ x ∧ n^2 = 63 - Real.sqrt x} = {3969, 3844, 3481, 2916, 2209, 1444, 729, 196} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First, assume there exists a natural n such that 0 ≤ x ∧ n^2 = 63 - Real.sqrt x
      rintro ⟨n, hx1, heq⟩
      have h2 : (Real.sqrt x) ≥ 0 := by
        apply Real.sqrt_nonneg
      have h3 : Real.sqrt x = (63 : ℝ) - (n : ℝ) ^ 2 := by linarith [heq]
      have h4 : (63 - (n : ℝ) ^ 2 : ℝ) ≥ 0 := by
        nlinarith [h2, h3]
      have h5 : n ≤ 7 := by
        by_contra h6
        push_neg at h6
        have h7 : n ≥ 8 := by omega
        have h8 : (n : ℝ) ≥ 8 := by
          exact_mod_cast h7
        nlinarith [h4, h8]
      have h6 : (Real.sqrt x) ^ 2 = x := by
        rw [Real.sq_sqrt]
        linarith
      have eq1 : x = ((63 - (n : ℝ) ^ 2) : ℝ) ^ 2 := by
        rw [show Real.sqrt x = (63 : ℝ) - (n : ℝ) ^ 2 by linarith [h3] ] at h6
        nlinarith
      have h7 : n ≤ 7 := h5
      have h8 : n ≥ 0 := by omega
      interval_cases n <;> norm_num at eq1 heq h4 <;> norm_num [eq1]
    · -- Now the reverse direction: each element in the finite set is in the original set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 3969
        use 0
        constructor
        · norm_num
        · -- Show 0^2 = 63 - sqrt(3969)
          have h63 : Real.sqrt (3969 : ℝ) = 63 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h63]
          all_goals norm_num
      · -- x = 3844
        use 1
        constructor
        · norm_num
        · -- Show 1^2 = 63 - sqrt(3844)
          have h62 : Real.sqrt (3844 : ℝ) = 62 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h62]
          all_goals norm_num
      · -- x = 3481
        use 2
        constructor
        · norm_num
        · -- Show 2^2 = 63 - sqrt(3481)
          have h59 : Real.sqrt (3481 : ℝ) = 59 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h59]
          all_goals norm_num
      · -- x = 2916
        use 3
        constructor
        · norm_num
        · -- Show 3^2 = 63 - sqrt(2916)
          have h54 : Real.sqrt (2916 : ℝ) = 54 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h54]
          all_goals norm_num
      · -- x = 2209
        use 4
        constructor
        · norm_num
        · -- Show 4^2 = 63 - sqrt(2209)
          have h47 : Real.sqrt (2209 : ℝ) = 47 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h47]
          all_goals norm_num
      · -- x = 1444
        use 5
        constructor
        · norm_num
        · -- Show 5^2 = 63 - sqrt(1444)
          have h38 : Real.sqrt (1444 : ℝ) = 38 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h38]
          all_goals norm_num
      · -- x = 729
        use 6
        constructor
        · norm_num
        · -- Show 6^2 = 63 - sqrt(729)
          have h27 : Real.sqrt (729 : ℝ) = 27 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h27]
          all_goals norm_num
      · -- x = 196
        use 7
        constructor
        · norm_num
        · -- Show 7^2 = 63 - sqrt(196)
          have h14 : Real.sqrt (196 : ℝ) = 14 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          rw [h14]
          all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> norm_num