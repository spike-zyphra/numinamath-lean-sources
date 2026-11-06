import Mathlib

theorem algebra_13602 (x : ℝ) (hx : Real.tan x = 3 / (2 * Real.sqrt 10)) :
    Real.cos (2 * x) = 31 / 49 := by
  have htan : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan] at hx
  have h6 : Real.cos x ≠ 0 := by 
    by_contra h
    rw [h] at hx
    field_simp [show 2 * Real.sqrt 10 ≠ 0 by 
      have hsqrt_pos : Real.sqrt 10 > 0 := Real.sqrt_pos.mpr (show (10 : ℝ) > 0 by norm_num)
      have hsqrt_nz : Real.sqrt 10 ≠ 0 := by positivity
      simp [hsqrt_nz]
    ] at hx 
    all_goals linarith 
  have h7 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := by 
    rw [Real.cos_two_mul]
  have h8 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq x 
  have h9 : Real.sin x = Real.cos x * (3 / (2 * Real.sqrt 10)) := by 
    field_simp [show Real.cos x ≠ 0 by exact h6] at hx 
    field_simp [show Real.sqrt 10 > 0 by 
      have hsqrt_pos : Real.sqrt 10 > 0 := Real.sqrt_pos.mpr (show (10 : ℝ) > 0 by norm_num)
      linarith 
    ] at hx ⊢ 
    <;> nlinarith 
  have hsin2 : Real.sin x ^ 2 = Real.cos x ^ 2 * (9 / 40) := by 
    calc 
      Real.sin x ^ 2 = (Real.cos x * (3 / (2 * Real.sqrt 10))) ^ 2 := by 
        rw [h9] 
        <;> all_goals nlinarith [Real.sq_sqrt (show (10 : ℝ) ≥ 0 by norm_num), Real.sqrt_pos.mpr (show (10 : ℝ) > 0 by norm_num)]
      _ = Real.cos x ^ 2 * (3 / (2 * Real.sqrt 10)) ^ 2 := by 
        ring_nf 
        <;> all_goals norm_num 
      _ = Real.cos x ^ 2 * (9 / 40) := by 
        have h2 : (3 / (2 * Real.sqrt 10)) ^ 2 = 9 / 40 := by 
          calc 
            (3 / (2 * Real.sqrt 10)) ^ 2 = 9 / ((2 * Real.sqrt 10) ^ 2) := by 
              field_simp 
              <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)] 
            _ = 9 / (4 * (Real.sqrt 10) ^ 2) := by 
              ring_nf 
              <;> all_goals norm_num 
            _ = 9 / (4 * 10) := by 
              have hsqrt : (Real.sqrt 10) ^ 2 = 10 := Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)
              rw [hsqrt] 
              all_goals norm_num 
            _ = 9 / 40 := by 
              all_goals norm_num 
        rw [h2] 
        all_goals linarith 
  have hcos2 : Real.cos x ^ 2 = 40 / 49 := by 
    nlinarith [h8, hsin2] 
  rw [h7]
  rw [hcos2]
  all_goals norm_num