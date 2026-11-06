import Mathlib

open Real Set
open scoped Real

theorem algebra_601866 :
  IsLeast {y | ∃ x, y = 5 / (2 * sin x ^ 2 + 3) + 8 / (5 * cos x ^ 2 + 6)} (81 / 37) := by 
  constructor
  · -- First part: Show existence.
    use Real.arccos (2 / 3)
    have h1 : cos (Real.arccos (2 / 3)) = 2 / 3 := by
      apply Real.cos_arccos
      all_goals norm_num
    have h2 : sin (Real.arccos (2 / 3)) ^ 2 = 5 / 9 := by
      have h3 : sin (Real.arccos (2 / 3)) ^ 2 + cos (Real.arccos (2 / 3)) ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq (Real.arccos (2 / 3))
      rw [h1] at h3
      nlinarith
    norm_num [h1, h2]
    all_goals norm_num [h1, h2]
  
  · -- Second part: Minimality.
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have eq1 : 2 * sin x ^ 2 + 3 = 5 - 2 * cos x ^ 2 := by 
      nlinarith [h3]
    
    have h4 : 5 / (2 * sin x ^ 2 + 3) + 8 / (5 * cos x ^ 2 + 6) ≥ 81 / 37 := by 
      have h5 : 0 < 2 * sin x ^ 2 + 3 := by
        nlinarith [Real.sin_sq_le_one x, Real.sin_sq_add_cos_sq x]
    
      have h6 : 0 < 5 * cos x ^ 2 + 6 := by
        nlinarith [Real.cos_sq_le_one x, Real.sin_sq_add_cos_sq x]
    
      have h7 : (5 / (2 * sin x ^ 2 + 3) + 8 / (5 * cos x ^ 2 + 6) ) - 81 / 37 ≥ 0 := by 
        have h11 : 0 < (2 * sin x ^ 2 + 3 : ℝ) := by
          nlinarith [Real.sin_sq_le_one x, Real.sin_sq_add_cos_sq x]
        have h12 : 0 < (5 * cos x ^ 2 + 6 : ℝ) := by
          nlinarith [Real.cos_sq_le_one x, Real.sin_sq_add_cos_sq x]
        have eq14 : (5 / (2 * sin x ^ 2 + 3) + 8 / (5 * cos x ^ 2 + 6) ) - 81 / 37 =
            ( 5 * (5 * cos x ^ 2 + 6) * 37 + 8 * (2 * sin x ^ 2 + 3) * 37 - 81 * (2 * sin x ^ 2 + 3) * (5 * cos x ^ 2 + 6) ) / 
            ( (2 * sin x ^ 2 + 3) * (5 * cos x ^ 2 + 6) * 37 ) := by 
          field_simp
          ring
        rw [eq14] at *
        apply div_nonneg
        have h15 : 5 * (5 * cos x ^ 2 + 6) * 37 + 8 * (2 * sin x ^ 2 + 3) * 37 - 81 * (2 * sin x ^ 2 + 3) * (5 * cos x ^ 2 + 6) ≥ 0 := by 
          have h16 : sin x ^ 2 = 1 - cos x ^ 2 := by 
            nlinarith [Real.sin_sq_add_cos_sq x]
          rw [h16]
          nlinarith [sq_nonneg (cos x ^ 2 - 4 / 9), sq_nonneg (1 - cos x ^ 2 - 5 / 9), Real.cos_sq_le_one x, sq_nonneg (cos x ^ 2 * (1 - cos x ^ 2)), mul_nonneg (show (0:ℝ) ≤ 1 - cos x ^ 2 by nlinarith [Real.sin_sq_le_one x]) (show (0:ℝ) ≤ cos x ^ 2 by nlinarith [Real.cos_sq_le_one x]), Real.sin_sq_le_one x]
        linarith
        all_goals positivity
  
      linarith
    linarith [hx, h4]