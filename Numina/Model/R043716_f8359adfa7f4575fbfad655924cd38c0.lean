import Mathlib

theorem algebra_325945 {x y : ℝ} (hx : x > 2) (hy : y > 1)
    (h : 36 / Real.sqrt (x - 2) + 4 / Real.sqrt (y - 1) + 4 * Real.sqrt (x - 2) +
      Real.sqrt (y - 1) - 28 = 0) :
    x = 11 ∧ y = 5 := by
  have h1 : Real.sqrt (x - 2) > 0 := by
    apply Real.sqrt_pos.mpr
    linarith
  have h2 : Real.sqrt (y - 1) > 0 := by
    apply Real.sqrt_pos.mpr
    linarith
  have h3 : (Real.sqrt (x - 2)) ^ 2 = x - 2 := by
    rw [Real.sq_sqrt]
    linarith
  have h4 : (Real.sqrt (y - 1)) ^ 2 = y - 1 := by
    rw [Real.sq_sqrt]
    linarith
  have eq1 : 36 / Real.sqrt (x - 2) + 4 * Real.sqrt (x - 2) + 4 / Real.sqrt (y - 1) + Real.sqrt (y - 1) = 28 := by
    linarith
  have h5 : 36 / Real.sqrt (x - 2) + 4 * Real.sqrt (x - 2) ≥ 24 := by
    have h6 : Real.sqrt (x - 2) > 0 := h1
    have h7 : 36 / Real.sqrt (x - 2) + 4 * Real.sqrt (x - 2) - 24 ≥ 0 := by
      have h8 : 36 / Real.sqrt (x - 2) + 4 * Real.sqrt (x - 2) - 24 = (4 * (Real.sqrt (x - 2) ) ^ 2 - 24 * Real.sqrt (x - 2) + 36) / Real.sqrt (x - 2) := by
        field_simp
        ring
      rw [h8] at *
      apply div_nonneg
      nlinarith [sq_nonneg (Real.sqrt (x - 2) - 3)]
      all_goals linarith
    linarith
  have h8 : 4 / Real.sqrt (y - 1) + Real.sqrt (y - 1) ≥ 4 := by
    have h9 : Real.sqrt (y - 1) > 0 := h2
    have h10 : 4 / Real.sqrt (y - 1) + Real.sqrt (y - 1) - 4 ≥ 0 := by
      have h11 : 4 / Real.sqrt (y - 1) + Real.sqrt (y - 1) - 4 = ( (Real.sqrt (y - 1) ) ^ 2 - 4 * Real.sqrt (y - 1) + 4) / Real.sqrt (y - 1) := by
        field_simp
        ring
      rw [h11] at *
      apply div_nonneg
      nlinarith [sq_nonneg (Real.sqrt (y - 1) - 2)]
      all_goals linarith
    linarith
  have h10 : 36 / Real.sqrt (x - 2) + 4 * Real.sqrt (x - 2) = 24 := by
    nlinarith [eq1, h5, h8]
  have h11 : 4 / Real.sqrt (y - 1) + Real.sqrt (y - 1) = 4 := by
    nlinarith [eq1, h5, h8]
  have eq3 : Real.sqrt (x - 2) = 3 := by
    field_simp at h10
    nlinarith [ Real.sqrt_nonneg (x - 2) ]
  have eq4 : Real.sqrt (y - 1) = 2 := by
    field_simp at h11
    nlinarith [ Real.sqrt_nonneg (y - 1) ]
  have eq5 : x - 2 = 9 := by
    have h_eq : (Real.sqrt (x - 2)) ^ 2 = 9 := by
      rw [eq3]
      norm_num
    have : (Real.sqrt (x - 2)) ^ 2 = x - 2 := by
      rw [Real.sq_sqrt]
      linarith
    linarith
  have eq6 : y - 1 = 4 := by
    have h_eq : (Real.sqrt (y - 1)) ^ 2 = 4 := by
      rw [eq4]
      norm_num
    have : (Real.sqrt (y - 1)) ^ 2 = y - 1 := by
      rw [Real.sq_sqrt]
      linarith
    linarith
  have hx' : x = 11 := by
    nlinarith
  have hy' : y = 5 := by
    nlinarith
  exact ⟨hx', hy'⟩