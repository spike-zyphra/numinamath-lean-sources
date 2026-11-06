import Mathlib

theorem calculus_18531 : Real.arcsin (-1/2) = -Real.pi/6 := by
  have h1 : Real.sin (-Real.pi / 6) = -1 / 2 := by
    have h2 : Real.sin (-Real.pi / 6) = - Real.sin (Real.pi / 6) := by
      rw [show -Real.pi / 6 = - (Real.pi / 6) by ring]
      rw [Real.sin_neg]
    have h3 : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
    rw [h2, h3]
    all_goals ring

  have h4 : Real.arcsin (-1 / 2) = -Real.pi / 6 := by
    have h5 : Real.sin (-Real.pi / 6) = -1 / 2 := h1
    have h9 : Real.arcsin (Real.sin (-Real.pi / 6)) = -Real.pi / 6 := by
      apply Real.arcsin_sin
      all_goals
        linarith [Real.pi_pos]
    rw [show Real.sin (-Real.pi / 6) = -1 / 2 by linarith [h1] ] at h9
    linarith

  exact h4