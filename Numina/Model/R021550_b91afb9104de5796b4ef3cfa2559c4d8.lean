import Mathlib

theorem number_theory_323927 : ¬(∀ a b : ℝ, Irrational a → Irrational b → Irrational (a^b)) := by
  intro h
  have h1 := h (Real.sqrt 2) (Real.sqrt 2) (by
    apply irrational_sqrt_two
  ) (by
    apply irrational_sqrt_two
  )
  have h2 := h ((Real.sqrt 2) ^ (Real.sqrt 2)) (Real.sqrt 2) h1 (by
    apply irrational_sqrt_two
  )
  have h3 : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = (2 : ℝ) := by
    have h4 : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = (Real.sqrt 2) ^ (Real.sqrt 2 * Real.sqrt 2) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals
        positivity
    have h5 : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
      calc
        Real.sqrt 2 * Real.sqrt 2 = (Real.sqrt 2) ^ 2 := by ring
        _ = (2 : ℝ) := by rw [Real.sq_sqrt]; positivity
    rw [h5] at h4
    have h6 : (Real.sqrt 2 : ℝ) ^ (2 : ℝ) = (2 : ℝ) := by
      calc
        (Real.sqrt 2 : ℝ) ^ (2 : ℝ) = ((Real.sqrt 2) ^ 2 : ℝ) := by norm_cast
        _ = (2 : ℝ) := by
          rw [Real.sq_sqrt]
          all_goals
            positivity
    rw [h6] at h4
    linarith
  rw [h3] at h2
  norm_num at h2