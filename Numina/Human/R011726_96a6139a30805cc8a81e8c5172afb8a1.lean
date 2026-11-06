import Mathlib

/- Example 20 (1998 National High School League Question) If the ellipse $x^{2}+4(y-a)^{2}=4$ intersects the parabola $x^{2}=2 y$, then the range of real number $a$ is $\qquad$ . -/

theorem algebra_288568 (a : ℝ) : (∃ x y, (x^2 + 4 * (y - a)^2 = 4 ∧ x^2 = 2 * y)) → (-1 ≤ a ∧ a ≤ 17 / 8) := by
--We assume the parabola and the ellipse intersect. Let x, y be the coordinates of one intersection point.
  intro h
  obtain ⟨x, y, h1, h2⟩ := h
  rw [h2] at h1
--Substituting y = x^2 / 2 into the equation of the ellipse gives us a quadratic equation in y.
  have eq_subst : 4 * y ^ 2 + (2 - 8 * a) * y + (4 * a ^ 2 - 4) = 0 := by
    ring_nf at h1
    ring_nf
    nth_rw 1 [← h1]
    ring_nf
  have eq_subst' := eq_subst
--We use that the discriminant of a quadratic equation is non-negative to find a first condition on a, namely that a ≤ 17/8.
  rw [(by ring_nf : y ^ 2 = y * y), quadratic_eq_zero_iff_discrim_eq_sq (by linarith), discrim] at eq_subst'
  set discr := (2 - 8 * a) ^ 2 - 4 * 4 * (4 * a ^ 2 - 4) with discr_def
  have discr_pos : discr ≥ 0 := by
    rw [eq_subst']
    positivity
  ring_nf at discr_pos
  field_simp at discr_pos
  rw [← le_div_iff₀ (by linarith)] at discr_pos
  have : (68 : ℝ) / 32 = 17 / 8 := by norm_num
  rw [this] at discr_pos
--We now use the fact that y = x^2 / 2, hence nonnegative, to find more conditions on a.
  have ynonneg : y ≥ 0 := by
    have : y = x ^ 2 / 2 := by
      rw [h2]
      ring_nf
    rw [this]
    positivity
--We use the formula for the solutions of a quadratic equation to find the possible values of y.
  have possible_y : y = (-(2 - 8 * a) + Real.sqrt discr) / 8 ∨ y = (-(2 - 8 * a) - Real.sqrt discr) / 8 := by
    rw [(by ring_nf : (2 * 4 * y + (2 - 8 * a)) ^ 2 = (2 * 4 * y + (2 - 8 * a)) * (2 * 4 * y + (2 - 8 * a)))] at eq_subst'
    have ysol := quadratic_eq_zero_iff (by linarith : (4 : ℝ) ≠ 0) eq_subst' y
    rw [(by ring_nf : y * y = y ^ 2)] at ysol
    rw [(by norm_num : (2 : ℝ) * 4 = 8)] at *
    rw [← (by ring_nf : (8 * y + (2 - 8 * a)) ^ 2 = (8 * y + (2 - 8 * a)) * (8 * y + (2 - 8 * a)))] at eq_subst'
    rw [eq_subst', Real.sqrt_sq_eq_abs]
    by_cases pos : 8 * y + (2 - 8 * a) ≥ 0
    · rw [abs_of_nonneg pos]
      rw [← ysol]
      exact eq_subst
    · push_neg at pos
      rw [abs_of_neg pos]
      symm
      rw [(by ring_nf : (-(2 - 8 * a) - -(8 * y + (2 - 8 * a))) = (-(2 - 8 * a) + (8 * y + (2 - 8 * a)))), (by ring_nf : (-(2 - 8 * a) + -(8 * y + (2 - 8 * a))) = (-(2 - 8 * a) - (8 * y + (2 - 8 * a))))]
      rw [← ysol]
      exact eq_subst
--We replace in y the value of the discriminant from the computation before, namely discriminant = 68 - 32 * a.
  have discr_calc : discr = 68 - 32 * a := by
    rw [discr_def]
    ring_nf
--We consider separately the two possible values of y.
  rcases possible_y with y1 | y2
--If y1 is nonnegative, we have that a must satify -1 ≤ a ≤ 1. Intersecting with the previous condition gives us -1 ≤ a ≤ 17/8.
  · rw [y1, discr_calc] at ynonneg
    field_simp at ynonneg
    rw [le_div_iff₀ (by linarith)] at ynonneg
    ring_nf at ynonneg
    have ynonneg' : 2 - a * 8 ≤ Real.sqrt (68 - a * 32) := by
      linarith
    by_cases hpos : 2 - a * 8 > 0
    · rw [Real.le_sqrt' hpos] at ynonneg'
      ring_nf at ynonneg'
      rw [le_tsub_iff_left (by linarith)] at ynonneg'
      ring_nf at ynonneg'
      rw [(by linarith : (68 : ℝ) = 4 + 64)] at ynonneg'
      simp only [add_le_add_iff_left, Nat.ofNat_pos, mul_le_iff_le_one_left, sq_le_one_iff_abs_le_one] at ynonneg'
      have range_a2 : -1 ≤ a ∧ a ≤ 1 := by
        by_cases ha : a ≥ 0
        · rw [abs_of_nonneg ha] at ynonneg'
          exact ⟨by linarith, by linarith⟩
        · push_neg at ha
          rw [abs_of_neg ha] at ynonneg'
          exact ⟨by linarith, by linarith⟩
      constructor
      · linarith
      · exact discr_pos
    · push_neg at hpos
      exact ⟨by linarith, by linarith⟩
--If also y2 is nonnegative, we have that a must satisfy a ≤ -1 or a ≥ 1. Intersecting with the previous condition gives us -1 ≤ a ≤ 17/8.
  · rw [y2, discr_calc] at ynonneg
    field_simp at ynonneg
    rw [le_div_iff₀ (by linarith)] at ynonneg
    ring_nf at ynonneg
    have ynonneg' : √(68 - a * 32) ≤ a * 8 - 2 := by
      linarith
    rw [Real.sqrt_le_left] at ynonneg'
    swap
    apply le_trans _ ynonneg'
    positivity
    ring_nf at ynonneg'
    simp only [tsub_le_iff_right] at ynonneg'
    ring_nf at ynonneg'
    rw [(by linarith : (68 : ℝ) = 4 + 64)] at ynonneg'
    simp only [add_le_add_iff_left, Nat.ofNat_pos, le_mul_iff_one_le_left, one_le_sq_iff_one_le_abs] at ynonneg'
    have range_a2 : a ≤ -1 ∨ a ≥ 1 := by
      by_cases ha : a ≥ 0
      · rw [abs_of_nonneg ha] at ynonneg'
        right
        linarith
      · push_neg at ha
        rw [abs_of_neg ha] at ynonneg'
        left
        linarith
    rcases range_a2 with h1 | h2
    · exfalso
      have : -2 + (a * 8 - √(68 - a * 32)) ≤ - 2 + a * 8 := by
        simp only [neg_add_le_iff_le_add, tsub_le_iff_right]
        rw [← add_assoc 2]
        ring_nf
        simp only [le_add_iff_nonneg_right, Real.sqrt_nonneg]
      have : 0 ≤ -2 + a * 8 := by linarith
      linarith
    · exact ⟨by linarith, by linarith⟩