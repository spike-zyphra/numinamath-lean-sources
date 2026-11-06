import Mathlib

open Real Set
open scoped Real

theorem algebra_306718 (x y z : ℝ)
  (h₀ : sin x + sin y + sin z = 0)
  (h₁ : cos x + cos y + cos z = 0) :
  sin (2 * x) + sin (2 * y) + sin (2 * z) = 0 ∧
  cos (2 * x) + cos (2 * y) + cos (2 * z) = 0 := by
  have h2 : sin z = - (sin x + sin y) := by linarith
  have h3 : cos z = - (cos x + cos y) := by linarith
  have h4 : sin z ^ 2 + cos z ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq z
  rw [h2, h3] at h4
  have h5 : sin x ^ 2 + sin y ^ 2 + sin x * sin y = cos x ^ 2 + cos y ^ 2 + cos x * cos y := by
    ring_nf at h4 ⊢
    nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq z]
  have h6 : sin (2 * x) = 2 * sin x * cos x := by
    rw [sin_two_mul]
  have h7 : sin (2 * y) = 2 * sin y * cos y := by
    rw [sin_two_mul]
  have h8 : sin (2 * z) = 2 * sin z * cos z := by
    rw [sin_two_mul]
  have h9 : cos (2 * x) = 2 * cos x ^ 2 - 1 := by
    rw [cos_two_mul]
  have h10 : cos (2 * y) = 2 * cos y ^ 2 - 1 := by
    rw [cos_two_mul]
  have h11 : cos (2 * z) = 2 * cos z ^ 2 - 1 := by
    rw [cos_two_mul]
  constructor
  · -- Proof of $\sin 2x + \sin 2y + \sin 2z = 0$
    rw [h6, h7, h8, h2, h3]
    nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq z, sq_nonneg (sin x - sin y), sq_nonneg (cos x - cos y), sq_nonneg (sin x + sin y), sq_nonneg (cos x + cos y), Real.sin_sq_add_cos_sq z, sq_nonneg (sin z), sq_nonneg (cos z)]
  · -- Proof of $\cos 2x + \cos 2y + \cos 2z = 0$
    rw [h9, h10, h11, h3]
    nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq z, sq_nonneg (sin x - sin y), sq_nonneg (cos x - cos y), sq_nonneg (sin x + sin y), sq_nonneg (cos x + cos y), Real.sin_sq_add_cos_sq z, sq_nonneg (sin z), sq_nonneg (cos z)]