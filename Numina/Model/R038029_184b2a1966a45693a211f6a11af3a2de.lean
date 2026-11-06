import Mathlib

theorem algebra_288908 (a : ℝ) (h : a = Real.tan α) :
    Real.tan (Real.pi / 2 - α) = 1 / a := by

  have h1 : Real.sin (Real.pi / 2 - α) = Real.cos α := by
    rw [Real.sin_pi_div_two_sub]
  have h2 : Real.cos (Real.pi / 2 - α) = Real.sin α := by
    rw [Real.cos_pi_div_two_sub]

  have h3 : Real.tan (Real.pi / 2 - α) = Real.sin (Real.pi / 2 - α) / Real.cos (Real.pi / 2 - α) := by 
    rw [Real.tan_eq_sin_div_cos]

  rw [h3, h1, h2]
  by_cases hcos : Real.cos α = 0
  · -- cos α = 0, so sin^2 α = 1
    have hsin2 : (Real.sin α) ^ 2 = 1 := by
      have h1 : (Real.sin α) ^ 2 + (Real.cos α) ^ 2 = 1 := Real.sin_sq_add_cos_sq α
      rw [hcos] at h1
      nlinarith

    have hsin : Real.sin α ≠ 0 := by
      by_contra h0
      have h1 : (Real.sin α) ^ 2 = 0 := by
        rw [h0]
        norm_num
      linarith 
    have htan0 : Real.tan α = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      rw [hcos]
      norm_num

    have ha0 : a = 0 := by
      linarith [h, htan0]

    have htan0' : Real.cos α / Real.sin α = 0 := by
      rw [hcos]
      norm_num

    rw [htan0', ha0]
    all_goals norm_num
  by_cases hsin : Real.sin α = 0
  · -- sin α = 0, cos α ≠ 0
    have htan0 : Real.tan α = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [hcos, hsin]

    have ha0 : a = 0 := by 
      linarith [h, htan0]

    have htan' : Real.cos α / Real.sin α = 0 := by
      rw [hsin]
      norm_num

    rw [htan', ha0]
    all_goals norm_num
  · -- sin α ≠ 0, cos α ≠ 0
    have hsin' : Real.sin α ≠ 0 := hsin
    have hcos' : Real.cos α ≠ 0 := hcos
    have htan : Real.tan α = Real.sin α / Real.cos α := by
      rw [Real.tan_eq_sin_div_cos]
    have eq1 : (Real.cos α / Real.sin α) = 1 / Real.tan α := by 
      rw [htan]
      field_simp [hsin', hcos']
    have eq2 : (Real.cos α / Real.sin α) = 1 / a := by 
      rw [eq1, h]
    linarith [eq2]