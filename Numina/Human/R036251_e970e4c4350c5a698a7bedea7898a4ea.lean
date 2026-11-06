import Mathlib
open Real Set

theorem algebra_196718 :
  IsGreatest ((λ t : ℝ => dist (40 * t) (16 * t ^ 2 + 9)) '' Icc 0 2) 16 := by 
    constructor 
    · norm_num
      use 1.25
      simp [dist] 
      norm_num
      
    · simp [dist]
      intro t ht
      rcases ht with ⟨a, ha, rfl⟩
      simp 
      cases abs_cases (40 * a - (16 * a ^ 2 + 9)) with 
      | inl h => nlinarith [ha.1, ha.2, sq_nonneg (a - 5 / 4)] 
      | inr h => nlinarith [ha.1, ha.2, sq_nonneg (a - 5 / 4)] 