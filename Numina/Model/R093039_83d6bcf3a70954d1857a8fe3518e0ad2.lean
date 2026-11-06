import Mathlib

open Real Set
open scoped Real

theorem algebra_12739 : IsGreatest {y | ∃ x : ℝ, y = cos x ^ 3 + sin x ^ 2 - cos x} (32/27) := by
  constructor
  · -- Show that 32/27 is had achievable, with x = arc cos (-1/3)
    use (Real.arccos (-1/3))
    have hcos : cos (Real.arccos (-1/3)) = -1/3 := by
      rw [Real.cos_arccos]
      all_goals norm_num
    have hsin2 : sin (Real.arccos (-1/3)) ^ 2 = 8/9 := by 
      have hsin2 : sin (Real.arccos (-1/3)) ^ 2 + cos (Real.arccos (-1/3)) ^ 2 = 1 := Real.sin_sq_add_cos_sq (Real.arccos (-1/3))
      rw [hcos] at hsin2 
      nlinarith 
    rw [hcos, hsin2]
    norm_num 
  · -- Show 32/27 is a upper bound 
    intro y 
    rintro ⟨x, hx⟩ 
    have h1 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
    nlinarith [sq_nonneg (cos x + 1/3), sq_nonneg (cos x - 1), sq_nonneg (cos x + 1),
      Real.cos_le_one x, Real.neg_one_le_cos x, sq_nonneg (cos x ^ 2 - 1/9),
      sq_nonneg (cos x - (-1/3)), sq_nonneg ((cos x + 1/3) * (cos x - 1)), sq_nonneg (cos x * (cos x + 1/3)), sq_nonneg (cos x * (cos x + 1))]