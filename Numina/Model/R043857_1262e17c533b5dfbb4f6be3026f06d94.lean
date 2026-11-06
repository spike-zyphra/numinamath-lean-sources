import Mathlib

open Real Set
open scoped Real

theorem inequalities_189914 :
  IsGreatest {t : ℝ | ∃ x y z : ℝ, t = sin x * sin y * sin z + cos x * cos y * cos z} 1 := by
  constructor
  · -- Show 1 is in the set.
    use 0, 0, 0
    norm_num
  · -- Show 1 is an upper bound
    intro t ht
    rcases ht with ⟨x, y, z, ht⟩
    have h1 : sin x * sin y * sin z + cos x * cos y * cos z ≤ 1 := by
      nlinarith [sq_nonneg (sin x - sin y - sin z),
          sq_nonneg (cos x - cos y - cos z),
          sq_nonneg (sin x + sin y + sin z),
          sq_nonneg (cos x + cos y + cos z),
          sq_nonneg (sin x * cos y * cos z - sin y * sin z * cos x),
          sq_nonneg (sin x * sin y * sin z - cos x * cos y * cos z),
          sq_nonneg (sin x - cos x), sq_nonneg (sin y - cos y), sq_nonneg (sin z - cos z),
          Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq z,
          mul_self_nonneg (sin x * sin y), mul_self_nonneg (sin x * sin z), mul_self_nonneg (sin y * sin z),
          mul_self_nonneg (cos x * cos y), mul_self_nonneg (cos x * cos z), mul_self_nonneg (cos y * cos z),
          sq_nonneg (sin x - cos x), sq_nonneg (sin y - cos y), sq_nonneg (sin z - cos z)]
    linarith