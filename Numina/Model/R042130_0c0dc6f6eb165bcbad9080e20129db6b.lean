import Mathlib

open Real Set
open scoped Real

theorem algebra_12194 : IsGreatest {y | ∃ x, y = sin x * cos x / (1 + sin x + cos x)} (sqrt 2 / 2 - 1 / 2) := by
  constructor
  · -- Show that `sqrt 2 / 2 - 1 / 2` is in the set
    use Real.pi / 4
    have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    rw [h1, h2]
    have h3 : 0 < Real.sqrt 2 := by positivity
    have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    field_simp [(show (1 + Real.sqrt 2 : ℝ) ≠ 0 by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    )
    ]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show that `sqrt 2 / 2 - 1 / 2` is the greatest element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hx]
    by_cases h : 1 + sin x + cos x = 0 
    · -- If the denominator is 0, then the expression is 0 in Lean
      rw [h]
      norm_num
      all_goals
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    · 
      have h4 : sin x * cos x / (1 + sin x + cos x) = ( (sin x + cos x) - 1 ) / 2 := by
        have h3 : 1 + sin x + cos x ≠ 0 := h
        field_simp [h3]
        nlinarith [Real.sin_sq_add_cos_sq x]
      rw [h4]
      have h4 : sin x + cos x ≤ Real.sqrt 2 := by
        nlinarith [sq_nonneg (sin x + cos x - Real.sqrt 2), sq_nonneg (sin x - cos x), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1), Real.sin_sq_add_cos_sq x]
      have h5 : ( (sin x + cos x) - 1 ) / 2 ≤ Real.sqrt 2 / 2 - 1 / 2 := by
        linarith
      linarith