import Mathlib

open Real Set
open scoped Real

theorem algebra_316249 (x y z : ℝ) (h₀ : sin x < sin y) (h₁ : sin y < sin z)
  (h₂ : ∃ d, sin y = sin x + d ∧ sin z = sin y + d) :
  ¬∃ d, cos y = cos x + d ∧ cos z = cos y + d := by
  rcases h₂ with ⟨d, h3, h4⟩
  intro h
  rcases h with ⟨d', h5, h6⟩
  have h6' : sin z = sin x + 2 * d := by
    nlinarith
  have h3' : sin y ^ 2 + cos y ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq y
  have h3x : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have h3z : sin z ^ 2 + cos z ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq z
  rw [show sin y = sin x + d by linarith [h3]] at h3'
  rw [show cos y = cos x + d' by linarith [h5]] at h3'
  rw [show sin z = sin x + 2 * d by linarith [h6', h3, h4]] at h3z
  rw [show cos z = cos x + 2 * d' by linarith [h6, h5]] at h3z
  nlinarith [sq_nonneg (sin x - sin y), sq_nonneg (sin y - sin z), sq_nonneg (cos x - cos y), sq_nonneg (cos y - cos z), Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq z, sq_pos_of_pos (show 0 < sin y - sin x by linarith), sq_pos_of_pos (show 0 < sin z - sin y by linarith), sq_nonneg (d), sq_nonneg (d')]