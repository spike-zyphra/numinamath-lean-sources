import Mathlib

open Real Set

theorem algebra_9034 (f : ℝ → ℝ) (hf : f = λ x => 2 * sin x + sin (2 * x)) :
    IsLeast (range f) (-3 * √3 / 2) := by 
  have h1 : ∀ x, f x = 2 * sin x + sin (2 * x) := by 
    intro x
    rw [hf]

  constructor
  · -- Show that -3 * √3 / 2 is in the range of f
    use (-Real.pi / 3)
    have h2 : f (-Real.pi / 3) = -3 * Real.sqrt 3 / 2 := by 
      rw [h1]
      have h3 : sin (-Real.pi / 3) = -Real.sqrt 3 / 2 := by 
        have h4 : sin (-Real.pi / 3) = - sin (Real.pi / 3) := by 
          rw [show -Real.pi / 3 = - (Real.pi / 3) by ring]
          rw [sin_neg]
        have h5 : sin (Real.pi / 3) = Real.sqrt 3 / 2 := sin_pi_div_three
        rw [h5] at h4
        linarith [h4]
      have h4 : sin (2 * (-Real.pi / 3)) = -Real.sqrt 3 / 2 := by
        have h3a : 2 * (-Real.pi / 3) = - (2 * Real.pi / 3) := by ring
        rw [h3a]
        have h3b : sin (- (2 * Real.pi / 3)) = -sin (2 * Real.pi / 3) := by 
          rw [sin_neg]
        have h3c : sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by 
          have h3d : 2 * Real.pi / 3 = Real.pi - (Real.pi / 3) := by ring
          rw [h3d]
          rw [sin_pi_sub]
          all_goals
            have h5 : sin (Real.pi / 3) = Real.sqrt 3 / 2 := sin_pi_div_three
            linarith
        rw [h3c] at h3b
        rw [h3b]
        all_goals
          linarith
      simp only [h3, h4]
      <;> linarith
    linarith [h2]
  
  · -- Show that -3 * √3 / 2 is the least element in the range
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h1 x] at hx 
    have h5 : 2 * sin x + sin (2 * x) ≥ -3 * Real.sqrt 3 / 2 := by 
      have h1a : sin (2 * x) = 2 * sin x * cos x := by 
        rw [sin_two_mul]
      rw [h1a]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
        Real.sqrt_nonneg 3, 
        sq_nonneg (sin x - Real.sqrt 3 / 2), 
        sq_nonneg (sin x + Real.sqrt 3 / 2), 
        sq_nonneg (cos x - 1 / 2), 
        sq_nonneg (cos x + 1), 
        sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        sq_nonneg (sin x - (-Real.sqrt 3 / 2)), 
        sq_nonneg (cos x - (-1 / 2)), 
        sin_sq_add_cos_sq x 
      ]
    linarith [h5, hx]