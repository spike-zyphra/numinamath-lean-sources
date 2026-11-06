import Mathlib

open Real Set
open scoped Real

theorem algebra_192752 : IsGreatest {x | ∃ t : ℝ, x = sqrt (1 + sin t) + sqrt (1 - sin t)} 2 := by
  constructor
  · -- Show 2 is in the set.
    use 0
    have h1 : sin (0 : ℝ) = 0 := by
      simp
    rw [h1]
    have h2 : sqrt (1 + (0 : ℝ)) = 1 := by
      rw [show (1 + (0 : ℝ) : ℝ) = (1 : ℝ) by norm_num]
      exact sqrt_one
    have h3 : sqrt (1 - (0 : ℝ)) = 1 := by
      rw [show (1 - (0 : ℝ) : ℝ) = (1 : ℝ) by norm_num]
      exact sqrt_one
    rw [h2, h3]
    all_goals norm_num
  · -- Show no greater element is in the set.
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h2 : (sqrt (1 + sin t) + sqrt (1 - sin t)) ^ 2 ≤ (4 : ℝ) := by
      have h2 : (sqrt (1 + sin t) + sqrt (1 - sin t)) ^ 2 =
          (sqrt (1 + sin t)) ^ 2 + (sqrt (1 - sin t)) ^ 2 + 2 * (sqrt (1 + sin t) * sqrt (1 - sin t)) := by
        ring
      rw [h2]
      have h3 : (sqrt (1 + sin t)) ^ 2 = 1 + sin t := by
        apply Real.sq_sqrt
        linarith [neg_one_le_sin t, sin_le_one t]
      have h4 : (sqrt (1 - sin t)) ^ 2 = 1 - sin t := by
        apply Real.sq_sqrt
        linarith [neg_one_le_sin t, sin_le_one t]
      have h5 : sqrt (1 + sin t) * sqrt (1 - sin t) = Real.sqrt ((1 + sin t) * (1 - sin t)) := by
        rw [← Real.sqrt_mul (by linarith [neg_one_le_sin t, sin_le_one t] ) ]
      have h6 : (1 + sin t) * (1 - sin t) ≤ (1 : ℝ) := by
        nlinarith [sq_nonneg (sin t), Real.cos_sq_add_sin_sq t, sq_nonneg (sin t - 0)]
      have h7 : Real.sqrt ((1 + sin t) * (1 - sin t)) ≤ (1 : ℝ) := by
        have h8 : (1 + sin t) * (1 - sin t) ≤ (1 : ℝ) := by
          nlinarith [sq_nonneg (sin t), Real.cos_sq_add_sin_sq t, sq_nonneg (sin t - 0)]
        have h9 : Real.sqrt ((1 + sin t) * (1 - sin t)) ≤ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
        have h10 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
        linarith [h10]
      nlinarith [h3, h4, h5, h7, Real.sqrt_nonneg ((1 + sin t) * (1 - sin t)), Real.sqrt_nonneg (1 + sin t), Real.sqrt_nonneg (1 - sin t), sq_nonneg (sqrt (1 + sin t) - sqrt (1 - sin t)), Real.sin_sq_add_cos_sq t ]
    have h2' : sqrt (1 + sin t) + sqrt (1 - sin t) ≤ (2 : ℝ) := by
      nlinarith [h2, sq_nonneg (sqrt (1 + sin t) + sqrt (1 - sin t) - 2), Real.sqrt_nonneg (1 + sin t), Real.sqrt_nonneg (1 - sin t), Real.sin_sq_add_cos_sq t]
    linarith [ht, h2']