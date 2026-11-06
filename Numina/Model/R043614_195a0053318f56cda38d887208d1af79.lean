import Mathlib

theorem algebra_248322 (x : ℝ) (hx₁ : x > -1) (hx₂ : x ≠ 0) :
    ((x + 1) ^ ((1 : ℝ) / 2) + 1) / ((x + 1) ^ ((1 : ℝ) / 2) - 1) *
    (((x + 1) ^ ((1 : ℝ) / 2) + 1) * (x + 1) ^ ((-1 : ℝ) / 2) -
    ((x + 1) ^ ((1 : ℝ) / 2) - 1) * (x + 1) ^ ((-1 : ℝ) / 2)) /
    (2 * ((x + 1) ^ ((1 : ℝ) / 2) + 1) ^ 2) =
    1 / (x * (x + 1) ^ ((1 : ℝ) / 2)) := by

  have h1 : (x + 1) ^ ((1 : ℝ) / 2) > 0 := by
    apply Real.rpow_pos_of_pos
    linarith
  have h2 : (x + 1) ^ ((1 : ℝ) / 2) - 1 ≠ 0 := by 
    by_contra h
    have h1_eq : (x + 1) ^ ((1 : ℝ) / 2) = 1 := by linarith
    have h3 : ((x + 1) ^ ((1 : ℝ) / 2)) ^ 2 = 1 := by
      rw [h1_eq]
      norm_num
    have h4 : ((x + 1) ^ ((1 : ℝ) / 2)) ^ 2 = x + 1 := by 
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num 
      all_goals linarith 
    have h5 : x + 1 = 1 := by 
      nlinarith 
    have h6 : x = 0 := by 
      linarith 
    contradiction 
  have eq1 : ((x + 1) ^ ((1 : ℝ) / 2) + 1) * (x + 1) ^ ((-1 : ℝ) / 2) - ((x + 1) ^ ((1 : ℝ) / 2) - 1) * (x + 1) ^ ((-1 : ℝ) / 2) = 2 * ((x + 1) ^ ((-1 : ℝ) / 2)) := by
    have eq2 : ((x + 1 : ℝ) ^ ((1 : ℝ) / 2) + 1) * (x + 1) ^ ((-1 : ℝ) / 2) - ((x + 1 : ℝ) ^ ((1 : ℝ) / 2) - 1) * (x + 1) ^ ((-1 : ℝ) / 2) =
        2 * ((x + 1) ^ ((-1 : ℝ) / 2)) := by 
      have eq3 : (x + 1) ^ ((-1 : ℝ) / 2) = ((x + 1) ^ ((1 : ℝ) / 2))⁻¹ := by 
        have h_pos : (x + 1 : ℝ) > 0 := by linarith 
        rw [← Real.rpow_neg] 
        norm_num 
        all_goals linarith 
      rw [eq3]
      field_simp [show (x + 1) ^ ((1 : ℝ) / 2) ≠ 0 by linarith [h1]]
      <;> ring 
    linarith [eq2]
  rw [eq1] 
  have h5_eq : ((x + 1) ^ ((1 : ℝ) / 2)) ^ 2 = x + 1 := by 
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num 
    all_goals linarith 
  have eq3 : ((x + 1) ^ ((1 : ℝ) / 2) - 1) * ((x + 1) ^ ((1 : ℝ) / 2) + 1) = x := by 
    calc 
      ((x + 1) ^ ((1 : ℝ) / 2) - 1) * ((x + 1) ^ ((1 : ℝ) / 2) + 1) = ((x + 1) ^ ((1 : ℝ) / 2)) ^ 2 - 1 := by ring 
      _ = x + 1 - 1 := by rw [h5_eq] 
      _ = x := by linarith 
  have h6_pos : 0 < x + 1 := by 
    linarith 
  have h56 : ((x + 1) ^ ((-1 : ℝ) / 2)) = ((x + 1) ^ ((1 : ℝ) / 2))⁻¹ := by 
    have h_pos : (x + 1 : ℝ) > 0 := by linarith 
    rw [← Real.rpow_neg] 
    norm_num 
    all_goals linarith
  field_simp [show (x + 1) ^ ((1 : ℝ) / 2) - 1 ≠ 0 by exact h2, show (x + 1 : ℝ) ^ ((1 : ℝ) / 2) + 1 ≠ 0 by positivity, show x ≠ 0 by exact hx₂, show x + 1 ≠ 0 by linarith, show ((x + 1) ^ ((-1 : ℝ) / 2) ) = ((x + 1) ^ ((1 : ℝ) / 2))⁻¹ by 
      have h_pos : (x + 1 : ℝ) > 0 := by linarith 
      rw [← Real.rpow_neg] 
      norm_num 
      all_goals linarith
   ]
  <;> 
  nlinarith [show 0 < x + 1 by linarith, show ((x + 1) ^ ((1 : ℝ) / 2) ) > 0 by linarith [h1], sq_pos_of_ne_zero (show x ≠ 0 by exact hx₂), sq_nonneg ((x + 1) ^ ((1 : ℝ) / 2) - 1), sq_nonneg ((x + 1) ^ ((1 : ℝ) / 2) + 1)]