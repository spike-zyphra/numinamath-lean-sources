import Mathlib

open Real Set
open scoped Real

theorem calculus_17083 :
  IsLeast {y : ℝ | ∃ x, y = (sin x ^ 6 + cos x ^ 6 + 1) / (sin x ^ 4 + cos x ^ 4 + 1)} (5 / 6) := by 
  constructor
  · -- Show 5/6 is in the set. Take x = π/4.
    use (Real.pi / 4)
    have hsin : sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have hcos : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    rw [hsin, hcos]
    have h1 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h2 : (Real.sqrt 2 / 2 : ℝ) ^ 6 = 1 / 8 := by
      calc
        (Real.sqrt 2 / 2 : ℝ) ^ 6 = ((Real.sqrt 2 / 2 : ℝ) ^ 2) ^ 3 := by ring
        _ = (1 / 2) ^ 3 := by rw [h1]
        _ = 1 / 8 := by norm_num
    have h3 : (Real.sqrt 2 / 2 : ℝ) ^ 4 = 1 / 4 := by
      calc
        (Real.sqrt 2 / 2 : ℝ) ^ 4 = ((Real.sqrt 2 / 2 : ℝ) ^ 2) ^ 2 := by ring
        _ = (1 / 2) ^ 2 := by rw [h1]
        _ = 1 / 4 := by norm_num
    norm_num [h2, h3]
  · -- Show no smaller value is in the set.
    intro y hy
    rcases hy with ⟨x, hx⟩
    have hx1 : (sin x ^ 6 + cos x ^ 6 + 1) / (sin x ^ 4 + cos x ^ 4 + 1) ≥ (5 / 6) := by
      have h2 : sin x ^ 4 + cos x ^ 4 + 1 > 0 := by 
        nlinarith [sq_nonneg (sin x), sq_nonneg (cos x), Real.sin_sq_add_cos_sq x]
      apply (le_div_iff₀ h2).mpr
      nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x * cos x), sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1), sq_nonneg (sin x ^ 2 - 1 / 2), sq_nonneg (cos x ^ 2 - 1 / 2), sq_nonneg (sin x * cos x - 1 / 2), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - cos x ^ 2)]
    linarith [hx, hx1]