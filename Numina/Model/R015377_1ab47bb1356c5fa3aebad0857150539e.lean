import Mathlib


open Real


theorem algebra_129315 (α β : ℝ) (h₀ : Real.tan α + Real.tan β = 25) (h₁ : 1 / Real.tan α + 1 / Real.tan β = 30) :
    Real.tan (α + β) = 150 := by

  have htanα : Real.tan α ≠ 0 := by
    by_contra h
    have h2 : Real.tan α + Real.tan β = 25 := h₀
    rw [show Real.tan α = 0 by linarith [h]] at h2
    have h3 : Real.tan β = 25 := by linarith
    rw [show Real.tan α = 0 by linarith [h], show Real.tan β = 25 by linarith [h3]] at h₁
    norm_num at h₁


  have htanβ : Real.tan β ≠ 0 := by
    by_contra h
    have h2 : Real.tan α + Real.tan β = 25 := h₀
    rw [show Real.tan β = 0 by linarith [h]] at h2
    have h3 : Real.tan α = 25 := by linarith
    rw [show Real.tan α = 25 by linarith [h3], show Real.tan β = 0 by linarith [h]] at h₁
    norm_num at h₁

  have htanαβ : Real.tan α * Real.tan β = 5 / 6 := by
    have eq2 : 1 / Real.tan α + 1 / Real.tan β = (Real.tan α + Real.tan β) / (Real.tan α * Real.tan β) := by 
      field_simp [htanα, htanβ]
      all_goals nlinarith
    rw [eq2] at h₁
    rw [show Real.tan α + Real.tan β = 25 by linarith [h₀]] at h₁
    have h2 : Real.tan α * Real.tan β ≠ 0 := by
      apply mul_ne_zero
      exact htanα
      exact htanβ
    have eq3 : Real.tan α * Real.tan β = 5 / 6 := by
      field_simp [h2] at h₁ ⊢
      nlinarith
    exact eq3

  have htan7 : Real.tan (α + β) = (Real.tan α + Real.tan β) / (1 - Real.tan α * Real.tan β) := by
    have htan6 : Real.tan (α + β) = (Real.tan α + Real.tan β) / (1 - Real.tan α * Real.tan β) := by
      have htan4 : Real.tan (α + β) = (sin α * cos β + cos α * sin β) / (cos α * cos β - sin α * sin β) := by
        rw [Real.tan_eq_sin_div_cos]
        have hsin : sin (α + β) = sin α * cos β + cos α * sin β := by 
          rw [sin_add]
        have hcos : cos (α + β) = cos α * cos β - sin α * sin β := by 
          rw [cos_add]
        rw [hsin, hcos]

      have htan5 : (Real.tan α + Real.tan β) / (1 - Real.tan α * Real.tan β) = (sin α * cos β + cos α * sin β) / (cos α * cos β - sin α * sin β) := by
        have htan2 : Real.tan α = sin α / cos α := by rw [Real.tan_eq_sin_div_cos]
        have htan3 : Real.tan β = sin β / cos β := by rw [Real.tan_eq_sin_div_cos]
        rw [htan2, htan3]
        have hcosp : cos α ≠ 0 := by
          by_contra h
          have htan0 : Real.tan α = 0 := by 
            rw [Real.tan_eq_sin_div_cos]
            simp [h]
          rw [htan0] at h₀ h₁
          have htanβ25 : Real.tan β = 25 := by linarith
          rw [htanβ25] at h₁
          field_simp [htan0] at h₁
          all_goals try { tauto }
        have hcosp2 : cos β ≠ 0 := by
          by_contra h
          have htan0 : Real.tan β = 0 := by 
            rw [Real.tan_eq_sin_div_cos]
            simp [h]
          rw [htan0] at h₀ h₁
          have htanα25 : Real.tan α = 25 := by linarith
          rw [htanα25] at h₁
          field_simp [htan0] at h₁
          all_goals try { tauto }
        field_simp [hcosp, hcosp2]
        all_goals ring
      linarith [htan4, htan5]
    linarith [htan6]

  rw [htan7]
  have htan9 : (Real.tan α + Real.tan β) / (1 - Real.tan α * Real.tan β) = 150 := by
    rw [show Real.tan α + Real.tan β = 25 by linarith, show Real.tan α * Real.tan β = 5 / 6 by linarith]
    norm_num
  linarith [htan9]