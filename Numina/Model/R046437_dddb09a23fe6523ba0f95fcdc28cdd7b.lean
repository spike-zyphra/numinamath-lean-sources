import Mathlib

theorem algebra_199591 (α : ℝ) (hα : Real.cos α = -99 / 101) (hα1 : 180 * Real.pi / 180 < α ∧ α < 270 * Real.pi / 180) :
    1 / Real.tan α = 99 / 20 := by
  have h1 : Real.sin α < 0 := by
    have h5 : α > Real.pi := by
      linarith [hα1.1, Real.pi_pos]
    have h6 : α < 2 * Real.pi := by
      linarith [hα1.2, Real.pi_pos]
    have h7 : Real.sin (α) < 0 := by
      have h8 : Real.sin (α) = - Real.sin (α - Real.pi) := by 
        have h12 : Real.sin (α) = Real.sin ( (α - Real.pi) + Real.pi) := by 
          ring_nf
        rw [h12]
        have h13 : Real.sin ( (α - Real.pi) + Real.pi ) = - Real.sin (α - Real.pi) := by
          rw [Real.sin_add, Real.sin_pi, Real.cos_pi]
          all_goals ring
        rw [h13]
      have h14 : Real.sin (α - Real.pi) > 0 := by 
        apply Real.sin_pos_of_pos_of_lt_pi
        all_goals linarith [Real.pi_pos]
      linarith [h8, h14]
    linarith [h7]
  -- Now, we compute sin α from the Pythagorean identity
  have h2 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α 
  rw [hα] at h2
  have h3 : Real.sin α = -20 / 101 := by
    nlinarith [h1]
  -- Now compute 1 / tan α and verify it's 99 / 20.
  have h4 : Real.tan α = Real.sin α / Real.cos α := by
    rw [Real.tan_eq_sin_div_cos]
  rw [h4]
  rw [h3, hα]
  all_goals norm_num