import Mathlib

theorem algebra_310850 (x y : ℝ) (h : ∀ α β, Real.cos α - Real.cos β ≠ 0 →
    (Real.sin (α + Real.pi / 6) + Real.sin (β - Real.pi / 6)) / (Real.cos α - Real.cos β) =
    x / Real.tan ((α - β) / 2) + y) :
    x = -Real.sqrt 3 / 2 ∧ y = 1 / 2 := by
  have eq1 := h 0 (Real.pi / 3) (by norm_num [Real.cos_pi_div_three])
  have eq2 := h (Real.pi / 2) (Real.pi / 6) (by
    have h1 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
    have h2 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
    intro hne
    rw [h1, h2] at hne
    norm_num at hne
  )
  have eq3 : (Real.sin (0 + Real.pi / 6) + Real.sin (Real.pi / 3 - Real.pi / 6)) / (Real.cos 0 - Real.cos (Real.pi / 3)) = 2 := by
    have h1 : Real.sin (0 + Real.pi / 6) = 1 / 2 := by
      rw [show 0 + Real.pi / 6 = Real.pi / 6 by ring]
      exact Real.sin_pi_div_six
    have h2 : Real.sin (Real.pi / 3 - Real.pi / 6) = 1 / 2 := by
      have h3 : Real.pi / 3 - Real.pi / 6 = Real.pi / 6 := by
        ring
      rw [h3]
      exact Real.sin_pi_div_six
    have h4 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
    have h5 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    rw [h1, h2, h4, h5]
    norm_num
  have eq4 : (Real.sin (Real.pi / 2 + Real.pi / 6) + Real.sin (Real.pi / 6 - Real.pi / 6)) / (Real.cos (Real.pi / 2) - Real.cos (Real.pi / 6)) = -1 := by
    have h1 : Real.sin (Real.pi / 2 + Real.pi / 6) = Real.sqrt 3 / 2 := by
      have h6 : Real.pi / 2 + Real.pi / 6 = 2 * Real.pi / 3 := by
        ring
      rw [h6]
      have h7 : Real.sin (2 * Real.pi / 3) = Real.sin (Real.pi - Real.pi / 3) := by
        ring_nf
      rw [h7]
      rw [Real.sin_pi_sub]
      have h8 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
      linarith [h8]
    have h2 : Real.sin (Real.pi / 6 - Real.pi / 6) = 0 := by
      simp
    have h3 : Real.cos (Real.pi / 2 : ℝ) = 0 := Real.cos_pi_div_two
    have h4 : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
    rw [h1, h2, h3, h4]
    field_simp
    <;> ring
  rw [eq3] at eq1
  rw [eq4] at eq2
  have htan1 : Real.tan ((0 - Real.pi / 3) / 2) = -1 / Real.sqrt 3 := by
    have h1 : (0 - Real.pi / 3) / 2 = - (Real.pi / 6) := by
      ring
    rw [h1]
    have h2 : Real.tan (- (Real.pi / 6)) = - Real.tan (Real.pi / 6) := by
      rw [Real.tan_neg]
    rw [h2]
    have h3 : Real.tan (Real.pi / 6) = 1 / Real.sqrt 3 := Real.tan_pi_div_six
    rw [h3]
    <;> ring
  have htan2 : Real.tan ((Real.pi / 2 - Real.pi / 6) / 2) = 1 / Real.sqrt 3 := by
    have h4 : (Real.pi / 2 - Real.pi / 6) / 2 = Real.pi / 6 := by
      ring_nf
    rw [h4]
    rw [Real.tan_pi_div_six]
  rw [htan1] at eq1
  rw [htan2] at eq2
  field_simp at eq1 eq2
  have eq5 : - Real.sqrt 3 * x + y = 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have eq6 : Real.sqrt 3 * x + y = -1 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have hy : y = 1 / 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have hx : x = - Real.sqrt 3 / 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  exact ⟨hx, hy⟩