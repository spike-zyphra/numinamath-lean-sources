import Mathlib

theorem algebra_12159 (x : ℝ) (hx : x ∈ Set.Ioo (-3 / 4 * Real.pi) (Real.pi / 4)) (h : Real.cos (Real.pi / 4 - x) = -3 / 5) :
    Real.cos (2 * x) = -24 / 25 := by
  rcases hx with ⟨hx1, hx2⟩
  -- Show that π/4 - x is in interval (0, π)
  have h1 : Real.sin (Real.pi / 4 - x) > 0 := by
    have h2 : Real.pi / 4 - x > 0 := by
      linarith
    have h3 : Real.pi / 4 - x < Real.pi := by
      linarith
    apply Real.sin_pos_of_pos_of_lt_pi 
    all_goals linarith
  have h2 : Real.sin (Real.pi / 4 - x) ^ 2 + Real.cos (Real.pi / 4 - x) ^ 2 = 1 := Real.sin_sq_add_cos_sq (Real.pi / 4 - x)
  rw [h] at h2 
  have hsin : Real.sin (Real.pi / 4 - x) = 4 / 5 := by
    nlinarith [h2, h1]
  have h3 : 2 * x = Real.pi / 2 - 2 * (Real.pi / 4 - x) := by
    ring
  rw [h3]
  rw [Real.cos_pi_div_two_sub]
  rw [Real.sin_two_mul (Real.pi / 4 - x)]
  rw [hsin, h]
  norm_num