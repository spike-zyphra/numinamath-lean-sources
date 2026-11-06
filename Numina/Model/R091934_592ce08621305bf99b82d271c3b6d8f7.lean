import Mathlib

theorem algebra_13404 : IsGreatest {x | ∃ t : ℝ, x = Real.cos t ^ 2 - 6 * Real.sin t - 12} (-6) := by
  constructor
  · -- Show that -6 belongs to the set
    use Real.pi * (3 / 2)
    have h1 : Real.cos (Real.pi * (3 / 2)) = 0 := by
      have h2 : Real.cos (Real.pi * (3 / 2)) = Real.cos (Real.pi + Real.pi / 2) := by
        ring_nf
      rw [h2]
      rw [Real.cos_add]
      simp [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
      all_goals linarith [Real.cos_sq_add_sin_sq (Real.pi / 2)]
    have h2 : Real.sin (Real.pi * (3 / 2)) = -1 := by
      have h3 : Real.sin (Real.pi * (3 / 2)) = Real.sin (Real.pi + Real.pi / 2) := by
        ring_nf
      rw [h3]
      rw [Real.sin_add]
      simp [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
      all_goals linarith [Real.cos_sq_add_sin_sq (Real.pi / 2)]
    rw [h1, h2]
    norm_num
  · -- Show that for any x in the set, x ≤ -6
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
    have h2 : -1 ≤ Real.sin t := by
      linarith [Real.neg_one_le_sin t, Real.sin_le_one t]
    have h3 : Real.sin t ≤ 1 := Real.sin_le_one t
    nlinarith [sq_nonneg (Real.sin t + 1), sq_nonneg (Real.sin t - 1), sq_nonneg (Real.cos t)]