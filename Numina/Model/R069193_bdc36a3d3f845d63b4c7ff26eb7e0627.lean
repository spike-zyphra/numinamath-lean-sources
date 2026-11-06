import Mathlib

open Real Set
open scoped Real

theorem algebra_246195 (x : ℝ) (h : 3 / (1 - sin x - cos x) = 4) :
    cos (4 * x) = -97 / 128 := by
  have h1 : 1 - sin x - cos x ≠ 0 := by
    intro h2
    rw [h2] at h
    norm_num at h
  -- Converting to polynomial equation.
  have eqn1 : 3 = 4 * (1 - sin x - cos x) := by
    field_simp [h1] at h
    nlinarith
  -- Solving to get equation for (sinx + cosx)
  have eqn2 : sin x + cos x = 1 / 4 := by
    nlinarith
  -- Solving for sin 2x.
  have h2 : sin (2 * x) = -15 / 16 := by
    have hsin : sin (2 * x) = 2 * sin x * cos x := by
      rw [sin_two_mul]
    rw [hsin]
    have eqn3 : 2 * sin x * cos x = -15 / 16 := by
      have eqn4 : (sin x + cos x) ^ 2 = 1 / 16 := by
        rw [eqn2]
        all_goals norm_num
      have eqn5 : (sin x + cos x) ^ 2 = sin x ^ 2 + cos x ^ 2 + 2 * (sin x * cos x) := by
        ring
      have eqn6 : sin x ^ 2 + cos x ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq x
      rw [eqn5] at eqn4
      rw [eqn6] at eqn4
      nlinarith
    linarith
  -- Now we need to compute cos 4x
  have h3 : cos (4 * x) = 1 - 2 * (sin (2 * x) ^ 2) := by
    have h4 : cos (4 * x) = cos (2 * (2 * x)) := by ring_nf
    rw [h4]
    have h5 : cos (2 * (2 * x)) = 1 - 2 * (sin (2 * x) ^ 2) := by
      rw [cos_two_mul]
      rw [sin_sq]
      <;> ring_nf <;> simp [sin_sq, cos_sq]
      all_goals nlinarith
    linarith
  -- Substitute the value of sin 2x
  rw [h3, h2]
  norm_num