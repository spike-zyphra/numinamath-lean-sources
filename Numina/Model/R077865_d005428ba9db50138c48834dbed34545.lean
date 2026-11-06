import Mathlib

open Real Set
open scoped Real

theorem algebra_323887 {f : ℝ → ℝ}
  (hf : f = λ x => sqrt (sin x ^ 4 + 4 * cos x ^ 2) - sqrt (cos x ^ 4 + 4 * sin x ^ 2)) :
  ∀ x, f x = cos (2 * x) := by
  intro x
  have h1 : sqrt (sin x ^ 4 + 4 * cos x ^ 2) = 1 + cos x ^ 2 := by
    have h2 : sin x ^ 4 + 4 * cos x ^ 2 = (1 + cos x ^ 2) ^ 2 := by
      have hsin : sin x ^ 2 + cos x ^ 2 = 1 := by
        exact sin_sq_add_cos_sq x
      have h3 : sin x ^ 4 = (sin x ^ 2) ^ 2 := by
        ring
      have h4 : sin x ^ 2 = 1 - cos x ^ 2 := by
        linarith [hsin]
      rw [h3, h4]
      nlinarith [hsin, sq_nonneg (sin x ^ 2), sq_nonneg (cos x ^ 2)]
    rw [h2]
    have h5 : sqrt ((1 + cos x ^ 2) ^ 2) = (1 + cos x ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg]
      nlinarith [sq_nonneg (1 + cos x ^ 2), sq_nonneg (cos x ^ 2)]
    exact h5
  have h2 : sqrt (cos x ^ 4 + 4 * sin x ^ 2) = 1 + sin x ^ 2 := by
    have h3 : cos x ^ 4 + 4 * sin x ^ 2 = (1 + sin x ^ 2) ^ 2 := by
      have hsin : sin x ^ 2 + cos x ^ 2 = 1 := by
        exact sin_sq_add_cos_sq x
      have h4 : cos x ^ 4 = (cos x ^ 2) ^ 2 := by
        ring
      have h5 : cos x ^ 2 = 1 - sin x ^ 2 := by
        linarith [hsin]
      rw [h4, h5]
      nlinarith [hsin, sq_nonneg (cos x ^ 2), sq_nonneg (sin x ^ 2)]
    rw [h3]
    have h5 : sqrt ((1 + sin x ^ 2) ^ 2) = (1 + sin x ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg]
      nlinarith [sq_nonneg (1 + sin x ^ 2), sq_nonneg (sin x ^ 2)]
    exact h5
  rw [hf]
  simp only [h1, h2]
  have hcos : cos (2 * x) = cos x ^ 2 - sin x ^ 2 := by
    rw [cos_two_mul, sin_sq]
    ring
  nlinarith [hcos, sin_sq_add_cos_sq x]