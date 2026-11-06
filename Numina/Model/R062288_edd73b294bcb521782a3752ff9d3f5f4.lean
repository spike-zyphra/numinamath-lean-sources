import Mathlib

open Real Set
open scoped Real

theorem algebra_158683 : IsGreatest {y | ∃ x : ℝ, y = (cos x)^3 + (sin x)^2 - cos x} (32/27) := by
  constructor
  · -- First, we'll show that 32/27 is in the set
    use (Real.pi - Real.arccos (1 / 3))
    
    have hcos : cos (Real.pi - Real.arccos (1 / 3)) = -1 / 3 := by
      rw [cos_pi_sub, cos_arccos]
      all_goals norm_num
      
    have hsin2 : (sin (Real.pi - Real.arccos (1 / 3)))^2 = 8 / 9 := by
      have h1 : sin (Real.pi - Real.arccos (1 / 3)) ^ 2 + cos (Real.pi - Real.arccos (1 / 3)) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq (Real.pi - Real.arccos (1 / 3))
      
      rw [hcos] at h1
      nlinarith [h1, Real.sin_sq_le_one (Real.pi - Real.arccos (1 / 3)), Real.cos_sq_le_one (Real.pi - Real.arccos (1 / 3))] 

    rw [hcos, hsin2]
    norm_num
  
  · -- Now we need to prove that for all y in the set, y ≤ 32 / 27
    intro y
    rintro ⟨x, hx⟩

    have h1 : (sin x)^2 = 1 - (cos x)^2 := by
      rw [←Real.sin_sq_add_cos_sq x]
      linarith

    rw [h1] at hx

    have h2 : -1 ≤ cos x ∧ cos x ≤ 1 := by
      constructor
      · exact Real.neg_one_le_cos x
      · exact Real.cos_le_one x

    nlinarith [sq_nonneg ((cos x + 1/3) : ℝ), sq_nonneg (cos x - 1 : ℝ), sq_nonneg ((cos x)^2 - 1 : ℝ)]