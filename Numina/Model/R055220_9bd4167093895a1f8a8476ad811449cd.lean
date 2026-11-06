import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_307346 :
  IsGreatest {x | ∃ t : ℝ, x = (cos t)^3 + (sin t)^2 - cos t} (32/27) := by
  constructor
  · -- Show 32/27 is in the set
    use Real.arccos (-1/3)
    have h : cos (Real.arccos (-1/3)) = -1/3 := by
      rw [Real.cos_arccos]
      norm_num
      all_goals linarith [Real.pi_pos]
    have h2 : sin (Real.arccos (-1/3)) = Real.sqrt (1 - (-1/3)^2) := by
      rw [Real.sin_arccos]
      <;> norm_num
    rw [h, h2]
    have h3 : (1 - (-1/3: ℝ)^2) = (8/9: ℝ) := by norm_num
    nlinarith [Real.sqrt_nonneg (1 - (-1/3)^2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 - (-1/3)^2) by norm_num)]
    <;> nlinarith
  · -- Show that 32/27 is the greatest element in the set 
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : cos t ^ 2 + sin t ^ 2 = 1 := by exact Real.cos_sq_add_sin_sq t
    have ht' : x = cos t ^ 3 + (1 - cos t ^ 2) - cos t := by
      have : sin t ^ 2 = 1 - cos t ^ 2 := by linarith
      rw [ht]
      linarith
    have hu1 : -1 ≤ cos t ∧ cos t ≤ 1 := by
      constructor
      · exact Real.neg_one_le_cos t
      · exact Real.cos_le_one t
    nlinarith [sq_nonneg (cos t + 1/3), sq_nonneg (cos t - 1), sq_nonneg (cos t + 1)]
    <;> nlinarith