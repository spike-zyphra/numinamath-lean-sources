import Mathlib

open Real

theorem algebra_248914 :
    {x : ℝ | x > 0 ∧ x ≠ 1 ∧ sqrt (x ^ logb 10 (sqrt x)) = 10} = {100, 1 / 100} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assuming x in {x : ℝ | x > 0 ∧ x ≠ 1 ∧ sqrt (x ^ logb 10 (sqrt x)) = 10}, proving x in {100, 1/100}
    rintro ⟨hx1, hx2, heq⟩
    have eq1 : x ^ logb 10 (sqrt x) = 100 := by
      calc
        x ^ logb 10 (sqrt x) = (sqrt (x ^ logb 10 (sqrt x))) ^ 2 := by 
          rw [Real.sq_sqrt]
          positivity
        _ = 10 ^ 2 := by
          rw [heq]
        _ = 100 := by norm_num
    have h2 : logb 10 (sqrt x) = (1 / 2) * logb 10 x := by 
      calc
        logb 10 (sqrt x) = logb 10 (x ^ (1 / 2 : ℝ)) := by 
          have h3 : sqrt x = x ^ (1 / 2 : ℝ) := by 
            rw [Real.sqrt_eq_rpow]
          rw [h3]
        _ = (1 / 2 : ℝ) * logb 10 x := by 
          rw [logb_rpow_eq_mul_logb_of_pos]
          all_goals linarith
    have h3 : logb 10 (x ^ logb 10 (sqrt x)) = logb 10 100 := by 
      rw [eq1]
    have h4 : logb 10 (x ^ logb 10 (sqrt x)) = logb 10 (sqrt x) * logb 10 x := by 
      rw [logb_rpow_eq_mul_logb_of_pos]
      all_goals linarith
    rw [h4] at h3
    rw [h2] at h3
    have h5 : logb 10 (100 : ℝ) = (2 : ℝ) := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    rw [h5] at h3
    have h6 : (logb 10 x) ^ 2 = 4 := by 
      nlinarith
    have h7 : logb 10 x = 2 ∨ logb 10 x = -2 := by 
      have h8 : (logb 10 x - 2) * (logb 10 x + 2) = 0 := by 
        nlinarith [h6]
      cases' (mul_eq_zero.mp h8) with h9 h10
      · left 
        linarith 
      · right 
        linarith 
    cases h7 with
    | inl h8 =>
      have h9 : x = (100 : ℝ) := by 
        have h10 : x = (10 : ℝ) ^ (logb 10 x : ℝ) := by 
          field_simp at *
          all_goals linarith 
        rw [h10, h8]
        norm_num 
      left 
      linarith 
    | inr h8 =>
      have h10 : x = (1 / 100 : ℝ) := by 
        have h11 : x = (10 : ℝ) ^ (logb 10 x : ℝ) := by 
          field_simp at *
          all_goals linarith 
        rw [h11, h8]
        norm_num 
      right 
      linarith 
  · -- Now the reverse direction
    rintro (h | h)
    · -- Case x = 100
      rw [h]
      constructor
      · norm_num 
      constructor 
      · norm_num 
      · -- Check the equation 
        have h8 : Real.sqrt ((100 : ℝ) ^ logb 10 (Real.sqrt (100 : ℝ)) ) = (10 : ℝ) := by 
          have h2 : Real.sqrt (100 : ℝ) = (10 : ℝ) := by 
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
          rw [h2] 
          have h3 : logb 10 (10 : ℝ) = (1 : ℝ) := by 
            rw [logb_eq_iff_rpow_eq] <;> norm_num 
          have h4 : (100 : ℝ) ^ logb 10 (10 : ℝ) = (100 : ℝ) ^ (1 : ℝ) := by 
            rw [h3] 
          have h5 : (100 : ℝ) ^ (1 : ℝ) = (100 : ℝ) := by 
            simp 
          rw [h4, h5] 
          have h6 : Real.sqrt (100 : ℝ) = (10 : ℝ) := by 
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
          exact h6 
        linarith [h8] 
    · -- Case x = 1/100 
      rw [h]
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · -- Check the equation 
        have h8 : Real.sqrt ((1 / 100 : ℝ) ^ logb 10 (Real.sqrt (1 / 100 : ℝ)) ) = (10 : ℝ) := by 
          have h2 : Real.sqrt (1 / 100 : ℝ) = (1 / 10 : ℝ) := by 
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
          rw [h2] 
          have h3 : logb 10 (1 / 10 : ℝ) = (-1 : ℝ) := by 
            rw [logb_eq_iff_rpow_eq] <;> norm_num 
          rw [h3] 
          have h5 : (1 / 100 : ℝ) ^ (-1 : ℝ) = (100 : ℝ) := by 
            norm_num 
          rw [h5] 
          have h6 : Real.sqrt (100 : ℝ) = (10 : ℝ) := by 
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
          exact h6 
        linarith [h8]