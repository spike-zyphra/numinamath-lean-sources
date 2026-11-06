import Mathlib

open Real Set
open scoped Real

theorem inequalities_36163 :
  IsGreatest {t : ℝ | ∃ x y z, t = sin x * cos y + sin y * cos z + sin z * cos x} (3 / 2) := by
  constructor
  · -- First, we verify that $3/2$ is indeed achievable, by setting $x = y = z = \pi/4$.
    use Real.pi / 4, Real.pi / 4, Real.pi / 4
    have hsin : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have hcos : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    rw [hsin, hcos]
    nlinarith [Real.sqrt_pos.mpr (show 0 < 2 by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
  · -- Now, we need to show that $3/2$ is indeed the greatest value.
    intro t ht
    rcases ht with ⟨x, y, z, ht⟩
    have h1 : sin x * cos y ≤ (sin x ^ 2 + cos y ^ 2) / 2 := by
      linarith [sq_nonneg (sin x - cos y)]
    have h2 : sin y * cos z ≤ (sin y ^ 2 + cos z ^ 2) / 2 := by
      linarith [sq_nonneg (sin y - cos z)]
    have h3 : sin z * cos x ≤ (sin z ^ 2 + cos x ^ 2) / 2 := by
      linarith [sq_nonneg (sin z - cos x)]
    have h4 : sin x ^ 2 + cos x ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq x
    have h5 : sin y ^ 2 + cos y ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq y
    have h6 : sin z ^ 2 + cos z ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq z
    nlinarith [ht, h1, h2, h3, h4, h5, h6]