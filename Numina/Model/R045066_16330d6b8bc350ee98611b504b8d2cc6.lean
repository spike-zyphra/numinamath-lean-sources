import Mathlib

open Real
open scoped Real

theorem inequalities_107488 (α β γ : ℝ) (h : α ∈ Set.Ioo 0 π)
  (h' : β ∈ Set.Ioo 0 π) (h'' : γ ∈ Set.Ioo 0 π) (h''' : α + β + γ = π) :
  3 * sqrt 3 ≤ 1 / tan (α / 2) + 1 / tan (β / 2) + 1 / tan (γ / 2) ∧
  (α ∈ Set.Ioo 0 (π / 2) ∧ β ∈ Set.Ioo 0 (π / 2) ∧ γ ∈ Set.Ioo 0 (π / 2)) →
  3 * sqrt 3 ≤ tan α + tan β + tan γ := by
  intro h
  rcases h with ⟨h1, ⟨ha1, hb1, hc1⟩⟩
  rcases ha1 with ⟨ha1l, ha1r⟩
  rcases hb1 with ⟨hb1l, hb1r⟩
  rcases hc1 with ⟨hc1l, hc1r⟩
  have htan1 : tan α > 0 := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    all_goals linarith
  have htan2 : tan β > 0 := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    all_goals linarith
  have ht13 : tan γ > 0 := by
    apply tan_pos_of_pos_of_lt_pi_div_two
    all_goals linarith
  -- Proof of tan α + tan β + tan γ = tan α * tan β * tan γ
  have htan4 : tan α + tan β + tan γ = tan α * tan β * tan γ := by
    have h2 : cos α > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      all_goals linarith
    have h3 : cos β > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      all_goals linarith
    have h4 : cos γ > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      all_goals linarith
    have h5 : sin α > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith
    have h6 : sin β > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith
    have h7 : sin γ > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith
    have htans : tan α = sin α / cos α := by rw [tan_eq_sin_div_cos]
    have htans' : tan β = sin β / cos β := by rw [tan_eq_sin_div_cos]
    have htans'' : tan γ = sin γ / cos γ := by rw [tan_eq_sin_div_cos]
    rw [htans, htans', htans'']
    have h9 : sin α * cos β * cos γ + cos α * sin β * cos γ + cos α * cos β * sin γ =
        sin α * sin β * sin γ := by
      have h9 : sin α * cos β * cos γ + cos α * sin β * cos γ + cos α * cos β * sin γ -
          sin α * sin β * sin γ = 0 := by
        have h10 : α + β + γ = π := h'''
        have h11 : sin (α + β + γ) = 0 := by
          rw [show α + β + γ = π by linarith]
          simp
        have h12 : sin (α + β + γ) = sin (α + β) * cos γ + cos (α + β) * sin γ := by
          rw [sin_add]
        rw [h12] at h11
        have h13 : sin (α + β) = sin α * cos β + cos α * sin β := by
          rw [sin_add]
        have h14 : cos (α + β) = cos α * cos β - sin α * sin β := by
          rw [cos_add]
        rw [h13, h14] at h11
        linarith
      linarith
    field_simp [show cos α ≠ 0 by linarith [h2], show cos β ≠ 0 by linarith [h3], show cos γ ≠ 0 by linarith [h4]] at *
    <;> linarith
  -- Now tan α + tan β + tan γ = tan α * tan β * tan γ. Let t = tan α + tan β + tan γ. Then t = tan α * tan β * tan γ. We need to show t ≥ 3 * sqrt 3. From AM-GM, we know that for a, b, c > 0, (a + b + c) /3 ≥ (abc)^(1/3). Thus, (a + b + c)³ / 27 ≥ abc, or (a + b + c)³ ≥ 27abc. But since t = (a + b + c) and t = abc, this gives t³ ≥ 27t, so t² ≥ 27 (for t > 0). Then t ≥ 3 * sqrt(3).
  have h5 : (tan α + tan β + tan γ) ^ 2 ≥ 27 := by 
    have h7 : tan α * tan β * tan γ = tan α + tan β + tan γ := by 
      linarith [htan4]
    nlinarith [sq_nonneg (tan α - tan β), sq_nonneg (tan α - tan γ), sq_nonneg (tan β - tan γ), 
          sq_nonneg (tan α * tan β - tan α * tan γ), sq_nonneg (tan α * tan β - tan β * tan γ), sq_nonneg (tan α * tan γ - tan β * tan γ), 
          h7, 
          mul_pos htan1 ht13, mul_pos ht13 ht13, mul_pos ht13 ht13, 
          mul_pos (show tan α > 0 by linarith) (show tan β > 0 by linarith), 
          mul_pos (show tan β > 0 by linarith) (show tan γ > 0 by linarith), 
          mul_pos (show tan α > 0 by linarith) (show tan γ > 0 by linarith)
        ]
  -- Now from t^2 >= 27. We have t^2 >= (3 * sqrt 3)^2. As t = tan α + tan β + tan γ > 0 and 3 * sqrt 3 > 0, we can take the square root to get t >= 3 * sqrt 3.
  have h6 : tan α + tan β + tan γ ≥ 3 * sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), h5, sq_nonneg (tan α + tan β + tan γ - 3 * sqrt 3)]
  linarith