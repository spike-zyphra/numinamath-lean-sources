import Mathlib

theorem algebra_319279 :
    Set.ncard {x : ℝ | x ≥ -19 ∧ x ≥ -95 ∧ Real.sqrt (x + 19) + (x + 95) ^ ((1 : ℝ) / 3) = 12} = 1 := by
  have h1 : {x : ℝ | x ≥ -19 ∧ x ≥ -95 ∧ Real.sqrt (x + 19) + (x + 95) ^ ((1 : ℝ) / 3) = 12} = {30} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume x in the solution set, show x = 30
      rintro ⟨hx1, hx2, heq⟩
      by_cases h : x < (30 : ℝ)
      · -- Assume x < 30
        -- Show that sqrt(x+19)+cbrt(x+95) < 12
        have h21 : Real.sqrt (x + 19) < (7 : ℝ) := by
          have h3 : x + 19 < (49 : ℝ) := by linarith
          have h4 : Real.sqrt (x + 19) < Real.sqrt (49 : ℝ) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
          have h5 : Real.sqrt (49 : ℝ) = (7 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          linarith [h4, h5]
        have h22 : (x + 95 : ℝ) ^ ((1 : ℝ) / 3) < (5 : ℝ) := by
          have h31 : x + 95 < (125 : ℝ) := by linarith
          have h41 : (x + 95 : ℝ) ^ ((1 : ℝ) / 3) < (125 : ℝ) ^ ((1 : ℝ) / 3) := by
            apply Real.rpow_lt_rpow
            all_goals linarith
          have h51 : (125 : ℝ) ^ ((1 : ℝ) / 3) = (5 : ℝ) := by
            have h3 : (125 : ℝ) = (5 : ℝ) ^ (3 : ℝ) := by norm_num
            rw [h3]
            have h4 : ((5 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (5 : ℝ) := by
              rw [← Real.rpow_mul]
              norm_num
              all_goals norm_num
            linarith [h4]
          linarith [h41, h51]
        have h6 : Real.sqrt (x + 19) + (x + 95) ^ ((1 : ℝ) / 3) < (12 : ℝ) := by
          linarith [h21, h22]
        linarith [h6, heq]
      by_cases h2 : x > (30 : ℝ)
      · -- Assume x > 30
        -- Show that sqrt(x+19)+cbrt(x+95) > 12
        have h31 : Real.sqrt (x + 19) > (7 : ℝ) := by
          have h42 : x + 19 > (49 : ℝ) := by linarith
          have h52 : Real.sqrt (x + 19) > Real.sqrt (49 : ℝ) := Real.sqrt_lt_sqrt (by linarith) (by linarith)
          have h62 : Real.sqrt (49 : ℝ) = (7 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          linarith [h52, h62]
        have h32 : (x + 95 : ℝ) ^ ((1 : ℝ) / 3) > (5 : ℝ) := by
          have h22 : x + 95 > (125 : ℝ) := by linarith
          have h32 : (x + 95 : ℝ) ^ ((1 : ℝ) / 3) > (125 : ℝ) ^ ((1 : ℝ) / 3) := by
            apply Real.rpow_lt_rpow
            all_goals linarith
          have h42 : (125 : ℝ) ^ ((1 : ℝ) / 3) = (5 : ℝ) := by
            have h33 : (125 : ℝ) = (5 : ℝ) ^ (3 : ℝ) := by norm_num
            rw [h33]
            have h43 : ((5 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (5 : ℝ) := by
              rw [← Real.rpow_mul]
              norm_num
              all_goals norm_num
            linarith [h43]
          linarith [h32, h42]
        have h7 : Real.sqrt (x + 19) + (x + 95) ^ ((1 : ℝ) / 3) > (12 : ℝ) := by
          linarith [h31, h32]
        linarith [h7, heq]
      linarith
    · -- Show that 30 is in the solution set
      intro hx
      rw [hx]
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Verify the equation.
        have h11 : Real.sqrt (30 + 19 : ℝ) = (7 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h12 : (30 + 95 : ℝ) ^ ((1 : ℝ) / 3) = (5 : ℝ) := by
          have h125 : (30 + 95 : ℝ) = (5 : ℝ) ^ (3 : ℝ) := by norm_num
          rw [h125]
          have h126 : ((5 : ℝ) ^ (3 : ℝ)) ^ ((1 : ℝ) / 3) = (5 : ℝ) := by
            rw [← Real.rpow_mul]
            norm_num
            all_goals norm_num
          linarith [h126]
        rw [h11, h12]
        all_goals norm_num
  rw [h1]
  simp