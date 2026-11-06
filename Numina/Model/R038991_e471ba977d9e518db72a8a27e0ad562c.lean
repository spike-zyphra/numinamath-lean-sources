import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_246792 :
  IsLeast {x : ℝ | ∃ s t : ℝ, x = (s + 5 - 3*abs (cos t))^2 + (s - 2*abs (sin t))^2} 2 := by
  constructor
  · -- Show 2 is in the set
    use -1, 0
    have h1 : abs (cos (0 : ℝ)) = 1 := by
      have hcos : cos (0 : ℝ) = 1 := cos_zero
      rw [hcos]
      all_goals norm_num
    have h2 : abs (sin (0 : ℝ)) = 0 := by 
      have hsin : sin (0 : ℝ) = 0 := sin_zero
      rw [hsin]
      all_goals norm_num
    rw [h1, h2]
    all_goals norm_num
  · -- Show 2 is the minimum
    intro x hx
    rcases hx with ⟨s, t, heq⟩
    have h1 : 0 ≤ abs (cos t) := by 
      apply abs_nonneg
    have h2 : 0 ≤ abs (sin t) := by 
      apply abs_nonneg
    have h3 : abs (cos t) ≤ 1 := by 
      apply abs_le.mpr
      constructor
      · -- Show -1 ≤ cos t
        linarith [neg_one_le_cos t, cos_le_one t]
      · -- Show cos t ≤ 1
        linarith [neg_one_le_cos t, cos_le_one t]
    have h4 : abs (sin t) ≤ 1 := by 
      apply abs_le.mpr
      constructor
      · -- Show -1 ≤ sin t
        linarith [neg_one_le_sin t, sin_le_one t]
      · -- Show sin t ≤ 1
        linarith [neg_one_le_sin t, sin_le_one t]
    nlinarith [sq_nonneg (s +1), sq_nonneg ( abs (sin t) -1 ), sq_nonneg ( abs (cos t) -1 ), abs_nonneg (sin t), abs_nonneg (cos t), 
          sq_nonneg (s +1), sq_nonneg ( abs (sin t) ), sq_nonneg ( abs (cos t) ), Real.sin_sq_add_cos_sq t, 
          mul_nonneg (abs_nonneg (sin t)) (abs_nonneg (cos t))
        ]