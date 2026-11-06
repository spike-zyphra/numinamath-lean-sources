import Mathlib
theorem algebra_241173 : Set.ncard {t : ℝ | ∃ x y z, (x ^ 2 - 9) ^ 2 + (y ^ 2 - 4) ^ 2 + (z ^ 2 - 1) ^ 2 = 0 ∧ x + y + z = t} = 7:= by
  have h1 : {t : ℝ | ∃ x y z, (x ^ 2 - 9) ^ 2 + (y ^ 2 - 4) ^ 2 + (z ^ 2 - 1) ^ 2 = 0 ∧ x + y + z = t} = {6, 4, 2, 0, -2, -4, -6} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume ∃ x y z, (x ^ 2 - 9) ^ 2 + (y ^ 2 - 4) ^ 2 + (z ^ 2 - 1) ^ 2 = 0 ∧ x + y + z = t
      rintro ⟨x, y, z, h_eq, h_eq2⟩
      have h2 : (x ^ 2 - 9) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x ^ 2 - 9), sq_nonneg (y ^ 2 - 4), sq_nonneg (z ^ 2 - 1)]
      have h3 : x ^ 2 - 9 = 0 := by
        rwa [sq_eq_zero_iff] at h2
      have h4 : x ^ 2 = 9 := by
        nlinarith [h3]
      have h5 : (y ^ 2 - 4) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x ^ 2 - 9), sq_nonneg (y ^ 2 - 4), sq_nonneg (z ^ 2 - 1)]
      have h6 : y ^ 2 - 4 = 0 := by
        rwa [sq_eq_zero_iff] at h5
      have h7 : y ^ 2 = 4 := by
        nlinarith [h6]
      have h8 : (z ^ 2 - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x ^ 2 - 9), sq_nonneg (y ^ 2 - 4), sq_nonneg (z ^ 2 - 1)]
      have h9 : z ^ 2 - 1 = 0 := by
        rwa [sq_eq_zero_iff] at h8
      have h10 : z ^ 2 = 1 := by
        nlinarith [h9]
      have h11 : x = 3 ∨ x = -3 := by
        have h11 : x ^ 2 = 9 := by
          linarith [h4]
        have : x = 3 ∨ x = -3 := by
          have h12 : x ^ 2 - 9 = 0 := by
            linarith [h3]
          have : (x - 3) * (x + 3) = 0 := by
            nlinarith [h12]
          cases' (mul_eq_zero.1 this) with h13 h14
          · -- Case x - 3 = 0, so x = 3
            left
            linarith [h13]
          · -- Case x + 3 = 0, so x = -3
            right
            linarith [h14]
        assumption
      have h12 : y = 2 ∨ y = -2 := by
        have h12 : y ^ 2 = 4 := by
          linarith [h7]
        have : y = 2 ∨ y = -2 := by
          have h13 : y ^ 2 - 4 = 0 := by
            linarith [h6]
          have : (y - 2) * (y + 2) = 0 := by
            nlinarith [h13]
          cases' (mul_eq_zero.1 this) with h14 h15
          · -- Case y - 2 = 0, so y = 2
            left
            linarith [h14]
          · --  Case y + 2 = 0, so y = -2
            right
            linarith [h15]
        assumption
      have h13 : z = 1 ∨ z = -1 := by
        have h13 : z ^ 2 = 1 := by
          linarith [h10]
        have : z = 1 ∨ z = -1 := by
          have h14 : z ^ 2 - 1 = 0 := by
            linarith [h9]
          have : (z - 1) * (z + 1) = 0 := by
            nlinarith [h14]
          cases' (mul_eq_zero.1 this) with h15 h16
          · -- Case z - 1 = 0, so z = 1
            left
            linarith [h15]
          · -- Case z + 1 = 0, so z = -1
            right
            linarith [h16]
        assumption
      rcases h11 with (h11 | h11) <;> rcases h12 with (h12 | h12) <;> rcases h13 with (h13 | h13) <;> 
        norm_num [h11, h12, h13] at h_eq2 ⊢
        <;> norm_num [h_eq2] at *
        <;> tauto
    · -- Assume t ∈ {6, 4, 2, 0, -2, -4, -6}, then $\exists x y z, (x ^ 2 - 9) ^ 2 + (y ^ 2 - 4) ^ 2 + (z ^ 2 - 1) ^ 2 = 0 ∧ x + y + z = t$
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- $t = 6$
        use 3, 2, 1
        norm_num
      · -- $t = 4$
        use 3, 2, -1
        norm_num
      · -- $t = 2$
        use 3, -2, 1
        norm_num
      · -- $t = 0$
        use 3, -2, -1
        norm_num
      · -- $t = -2$
        use -3, 2, -1
        norm_num
      · -- $t = -4$
        use -3, -2, 1
        norm_num
      · -- $t = -6$
        use -3, -2, -1
        norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]