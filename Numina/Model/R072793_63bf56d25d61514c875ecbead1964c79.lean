import Mathlib

open Real Set
open scoped Real

theorem algebra_113743 {f : ℝ → ℝ} (hf : f = λ x => cos x ^ 3 + sin x ^ 2 - cos x) :
    IsGreatest (range f) (32/27) := by
  constructor
  -- First show that 32/27 is attained
  · use (Real.arccos (-1 / 3))
    rw [hf]
    have hcos : cos (Real.arccos (-1 / 3)) = -1 / 3 := by
      apply Real.cos_arccos
      all_goals norm_num
    have hsin2 : sin (Real.arccos (-1 / 3)) ^ 2 = 8 / 9 := by
      have hsin : sin (Real.arccos (-1 / 3)) ^ 2 + cos (Real.arccos (-1 / 3)) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq (Real.arccos (-1 / 3))
      rw [hcos] at hsin
      nlinarith
    simp [hsin2, hcos]
    all_goals norm_num
  -- Now show that for all y in the range, y ≤ 32/27
  · intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    nlinarith [Real.sin_sq_add_cos_sq x, 
      sq_nonneg (cos x + 1/3), 
      sq_nonneg (cos x - 1), 
      sq_nonneg (cos x + 1)
    ]