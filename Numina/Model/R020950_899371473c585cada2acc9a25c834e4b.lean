import Mathlib

open Real Set
open scoped Real

theorem calculus_16898 :
  IsLeast {x | ∃ t : ℝ, x = (sin t)^4 + (cos t)^4} (1/2) := by
  constructor
  · -- Show that 1/2 is in the set.
    use Real.pi / 4
    have hsin : sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have hcos : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    rw [hsin, hcos]
    have h1 : (Real.sqrt 2 / 2 : ℝ) ^ 4 = (1 / 4 : ℝ) := by
      calc
        (Real.sqrt 2 / 2 : ℝ) ^ 4 = (Real.sqrt 2 ^ 4) / (2 ^ 4 : ℝ) := by ring_nf
        _ = (4 : ℝ) / (16 : ℝ) := by
          have h1 : Real.sqrt 2 ^ 4 = 4 := by
            calc
              Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
              _ = (2 : ℝ) ^ 2 := by rw [Real.sq_sqrt]; linarith
              _ = (4 : ℝ) := by norm_num
          rw [h1]
          all_goals norm_num
        _ = (1 / 4 : ℝ) := by norm_num
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  · -- Show that 1/2 is the least element in the set.
    intro x hx
    rcases hx with ⟨t, ht⟩
    rw [ht]
    have h1 : sin t ^ 4 + cos t ^ 4 ≥ 1 / 2 := by
      have h2 : sin t ^ 2 + cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
      nlinarith [sq_nonneg (sin t ^ 2 - cos t ^ 2), sq_nonneg (sin t * cos t), sq_nonneg (sin t - cos t), sq_nonneg (sin t + cos t)]
    linarith