import Mathlib

theorem algebra_260320 :
  {x : ℝ | (16 : ℝ)^x + (16 : ℝ)^(1 - x) = 10} = {1/4, 3/4} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First direction: if x is a solution, then x ∈ {1/4, 3/4}
    intro h_eq
    have h1 : (16 : ℝ) ^ (1 - x) = (16 : ℝ) / (16 : ℝ) ^ x := by
      rw [show 1 - x = 1 - x by ring]
      rw [Real.rpow_sub]
      ring_nf
      all_goals norm_num
    rw [h1] at h_eq
    have h2 : (16 : ℝ) ^ x > 0 := by positivity
    have h3 : ((16 : ℝ) ^ x) ^ 2 - 10 * ((16 : ℝ) ^ x) + 16 = 0 := by
      have h4 : ((16 : ℝ) ^ x) > 0 := by positivity
      have h5 : ((16 : ℝ) ^ x) ^ 2 + 16 = 10 * ((16 : ℝ) ^ x) := by
        field_simp at h_eq ⊢
        nlinarith [h_eq, h4]
      nlinarith
    have h4 : ((16 : ℝ) ^ x - 8) * ((16 : ℝ) ^ x - 2) = 0 := by
      nlinarith [h3]
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case h5: (16 : ℝ) ^ x - 8 = 0
      have h7 : (16 : ℝ) ^ x = 8 := by linarith
      have h8 : x = 3 / 4 := by
        have h9 : (16 : ℝ) ^ x = 8 := h7
        have h10 : x * (4 : ℝ) = 3 := by
          have h11 : (16 : ℝ) ^ x = 8 := h9
          have h12 : (16 : ℝ) ^ x = (2 : ℝ) ^ (4 * x) := by
            rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
            rw [← Real.rpow_mul]
            ring_nf
            all_goals linarith
          rw [h12] at h11
          have h13 : (2 : ℝ) ^ (4 * x) = (2 : ℝ) ^ (3 : ℝ) := by
            rw [h11]
            norm_num
          have h14 : 4 * x = (3 : ℝ) := by
            apply_fun (Real.logb (2 : ℝ)) at h13
            simp at h13 ⊢
            linarith
          linarith
        linarith
      right
      linarith
    · -- Case h6: (16 : ℝ) ^ x - 2 = 0
      have h7 : (16 : ℝ) ^ x = 2 := by linarith
      have h8 : x = 1 / 4 := by
        have h9 : (16 : ℝ) ^ x = 2 := h7
        have h10 : x * (4 : ℝ) = 1 := by
          have h11 : (16 : ℝ) ^ x = 2 := h9
          have h12 : (16 : ℝ) ^ x = (2 : ℝ) ^ (4 * x) := by
            rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
            rw [← Real.rpow_mul]
            ring_nf
            all_goals linarith
          rw [h12] at h11
          have h13 : (2 : ℝ) ^ (4 * x) = (2 : ℝ) ^ (1 : ℝ) := by
            rw [h11]
            norm_num
          have h14 : 4 * x = (1 : ℝ) := by
            apply_fun (Real.logb (2 : ℝ)) at h13
            simp at h13 ⊢
            linarith
          linarith
        linarith
      left
      linarith
  · -- Second direction: if x ∈ {1/4, 3/4}, then x is a solution
    rintro (h_eq | h_eq)
    · -- Case x = 1/4
      rw [h_eq]
      have h1 : (16 : ℝ) ^ ((1 / 4 : ℝ)) = 2 := by
        rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      have h2 : (16 : ℝ) ^ (1 - (1 / 4 : ℝ)) = 8 := by
        have h3 : (1 - (1 / 4 : ℝ) ) = (3 / 4 : ℝ) := by norm_num
        rw [h3]
        have h4 : (16 : ℝ) ^ (3 / 4 : ℝ) = 8 := by
          rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          norm_num
          all_goals norm_num
        exact_mod_cast h4
      rw [h1, h2]
      all_goals norm_num
    · -- Case x = 3/4
      rw [h_eq]
      have h1 : (16 : ℝ) ^ ((3 / 4 : ℝ)) = 8 := by
        rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      have h2 : (16 : ℝ) ^ (1 - (3 / 4 : ℝ)) = 2 := by
        have h3 : (1 - (3 / 4 : ℝ) ) = (1 / 4 : ℝ) := by norm_num
        rw [h3]
        have h4 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
          rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
          rw [← Real.rpow_mul]
          norm_num
          all_goals norm_num
        exact_mod_cast h4
      rw [h1, h2]
      all_goals norm_num