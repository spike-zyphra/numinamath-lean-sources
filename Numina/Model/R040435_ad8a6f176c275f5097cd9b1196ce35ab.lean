import Mathlib

theorem algebra_2422 (cbrt : ℝ → ℝ) (cbrt_pos : ∀ x ≥ 0, cbrt x = x ^ (1 / 3 : ℝ)) (cbrt_neg : ∀ x < 0, cbrt x = -(-x) ^ (1 / 3 : ℝ)) :
    ∑ᶠ x ∈ {x : ℝ | cbrt x = 6 / (1 + cbrt x)}, x = -19 := by
  have h1 : {x : ℝ | cbrt x = 6 / (1 + cbrt x)} = {-27, 8} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x satisfies the equation: cbrt x = 6 / (1 + cbrt x)
      intro h_eq
      have h2 : cbrt x ≠ -1 := by
        by_contra h
        rw [h] at h_eq
        field_simp at h_eq
      have h3 : cbrt x * (1 + cbrt x) = 6 := by
        field_simp [show 1 + cbrt x ≠ 0 by
          intro h0
          have h0' : cbrt x = -1 := by linarith
          contradiction] at h_eq ⊢
        linarith
      have h4 : (cbrt x - 2) * (cbrt x + 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- Case where cbrt x = 2
        have h7 : cbrt x = 2 := by linarith
        have h8 : x = 8 := by
          have h3 : cbrt x = 2 := h7
          have h9 : x ≥ 0 := by
            by_contra h
            push_neg at h
            have h10 : x < 0 := h
            rw [cbrt_neg x h10] at h3
            have h4' : (-x : ℝ) ^ (1 / 3 : ℝ) = -2 := by linarith
            have h5' : (-x : ℝ) ≥ 0 := by linarith
            have h6' : (-x : ℝ) ^ (1 / 3 : ℝ) ≥ 0 := by
              apply Real.rpow_nonneg
              linarith
            linarith
          rw [cbrt_pos x h9] at h3
          have h11 : x = 8 := by
            have h12 : x ^ (1 / 3 : ℝ) = 2 := h3
            have h14 : x = ((x ^ (1 / 3 : ℝ)) ^ 3) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul]
              norm_num
              all_goals linarith
            rw [h12] at h14
            norm_num at h14 ⊢
            linarith
          linarith
        right
        tauto
      · -- Case where cbrt x = -3
        have h7 : cbrt x = -3 := by linarith
        have h8 : x = -27 := by
          have h3 : cbrt x = -3 := h7
          have h8' : x < 0 := by
            by_contra h
            push_neg at h
            have h9 : x ≥ 0 := by linarith
            have h11 : cbrt x ≥ 0 := by
              rw [cbrt_pos x h9]
              positivity
            linarith
          rw [cbrt_neg x h8'] at h3
          have h9 : (-x : ℝ) ^ (1 / 3 : ℝ) = 3 := by linarith
          have h11 : -x = 27 := by
            have h12 : (-x : ℝ) ^ (1 / 3 : ℝ) = 3 := h9
            have h13 : (-x : ℝ) = ((-x : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul]
              norm_num
              all_goals nlinarith
            rw [h12] at h13
            norm_num at h13 ⊢
            linarith
          linarith
        left
        tauto
    · -- Reverse: if x ∈ |-27, 8| then it's a solution.
      rintro (h_eq | h_eq)
      · -- Case where x = -27
        rw [h_eq]
        have h1 : cbrt (-27 : ℝ) = -3 := by
          rw [cbrt_neg (-27 : ℝ) (by norm_num)]
          have h2 : (-(-27 : ℝ) : ℝ) ^ (1 / 3 : ℝ) = 3 := by
            have h3 : (-(-27 : ℝ) : ℝ) = 27 := by norm_num
            rw [h3]
            have h4 : (27 : ℝ) ^ (1 / 3 : ℝ) = 3 := by
              have h5 : (27 : ℝ) = (3 : ℝ) ^ 3 := by norm_num
              rw [h5]
              rw [← Real.rpow_natCast, ← Real.rpow_mul]
              norm_num
              all_goals norm_num
            linarith
          linarith
        rw [h1]
        norm_num
      · -- Case where x = 8
        rw [h_eq]
        have h1 : cbrt (8 : ℝ) = 2 := by
          rw [cbrt_pos 8 (by norm_num)]
          have h2 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
            have h3 : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
            rw [h3]
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            norm_num
            all_goals norm_num
          linarith
        rw [h1]
        norm_num
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num