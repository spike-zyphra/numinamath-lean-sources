import Mathlib
open Real Set

theorem algebra_196718 :
  IsGreatest ((λ t : ℝ => dist (40 * t) (16 * t ^ 2 + 9)) '' Icc 0 2) 16 := by
  constructor
  · -- Show that 16 is in the image of the function over the interval.
    use 1.25
    constructor
    · -- Show that 1.25 is in the interval [0, 2].
      norm_num
      all_goals norm_num
    · -- Calculate the distance at t = 1.25 and show it equals 16.
      norm_num [dist]
      all_goals norm_num [abs]
      all_goals norm_num [abs]
  · -- Show that 16 is the greatest distance in the image.
    intro y hy
    rcases hy with ⟨t, ht, rfl⟩
    simp [dist] at *
    have h1 : 0 ≤ t := by
      have h1 : t ∈ Icc (0 : ℝ) 2 := ht
      simp at h1 ⊢
      all_goals linarith
    have h2 : t ≤ (2 : ℝ) := by
      have h1 : t ∈ Icc (0 : ℝ) 2 := ht
      simp at h1 ⊢
      all_goals linarith
    -- We need to show that |40t - (16t² + 9)| ≤ 16
    have h3 : - (16 * t ^ 2 + 9) + 40 * t ≤ (16 : ℝ) := by
      nlinarith [sq_nonneg (t - (1.25 : ℝ)), sq_nonneg (t - (1.25 : ℝ)), sq_nonneg (t - 0 : ℝ), sq_nonneg (t - 2 : ℝ)]
    -- Show the lower bound
    have h4 : - (16 : ℝ) ≤ - (16 * t ^ 2 + 9) + 40 * t := by
      nlinarith [sq_nonneg (t - (1.25 : ℝ)), sq_nonneg (t - (1.25 : ℝ)), sq_nonneg (t - 0 : ℝ), sq_nonneg (t - 2 : ℝ)]
    apply abs_le.mpr
    constructor
    · -- Show -16 ≤ difference
      linarith
    · -- Show difference ≤ 16
      linarith