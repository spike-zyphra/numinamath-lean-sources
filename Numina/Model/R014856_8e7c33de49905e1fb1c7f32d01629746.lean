import Mathlib


open Real Set


theorem inequalities_598858 (α β : ℝ) (h : sin α * cos α * sin β * cos β ≠ 0) :
    1 / sin α ^ 2 + 1 / (cos α ^ 2 * sin β ^ 2 * cos β ^ 2) ≥ 9 := by

  have h1 : sin α ≠ 0 := by
    by_contra h11
    have h12 : sin α * cos α * sin β * cos β = 0 := by
      rw [h11]
      norm_num
    tauto

  have h2 : cos α ≠ 0 := by
    by_contra h21
    have h22 : sin α * cos α * sin β * cos β = 0 := by
      rw [h21]
      norm_num
    tauto

  have h3 : sin β ≠ 0 := by
    by_contra h31
    have h32 : sin α * cos α * sin β * cos β = 0 := by
      rw [h31]
      norm_num
    tauto

  have h4 : cos β ≠ 0 := by
    by_contra h41
    have h42 : sin α * cos α * sin β * cos β = 0 := by
      rw [h41]
      norm_num
    tauto

  have h5 : sin α ^ 2 > 0 := by
    have h6 : sin α ≠ 0 := h1
    positivity

  have h6 : cos α ^ 2 > 0 := by
    have h61 : cos α ≠ 0 := h2
    positivity

  have h7 : sin β ^ 2 > 0 := by
    have h8 : sin β ≠ 0 := h3
    positivity

  have h8 : cos β ^ 2 > 0 := by
    have h9 : cos β ≠ 0 := h4
    positivity

  have h10 : sin β ^ 2 * cos β ^ 2 ≤ 1 / 4 := by
    have h11 : sin β ^ 2 + cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
    nlinarith [sq_nonneg (sin β ^ 2 - cos β ^ 2), sq_nonneg (sin β * cos β), h7, h8]

  have h11 : cos α ^ 2 = 1 - sin α ^ 2 := by
    have h12 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    linarith

  have h3' : 1 / sin α ^ 2 + 1 / (cos α ^ 2 * sin β ^ 2 * cos β ^ 2) - 9 ≥ 0 := by
    have h13 : cos α ^ 2 * sin β ^ 2 * cos β ^ 2 > 0 := by positivity
    have h14 : sin α ^ 2 > 0 := h5
    have h15 : cos α ^ 2 > 0 := h6
    have h16 : sin β ^ 2 * cos β ^ 2 > 0 := by positivity

    have h17 : 1 / sin α ^ 2 + 1 / (cos α ^ 2 * sin β ^ 2 * cos β ^ 2) - 9 = (cos α ^ 2 * sin β ^ 2 * cos β ^ 2 + sin α ^ 2 - 9 * sin α ^ 2 * cos α ^ 2 * sin β ^ 2 * cos β ^ 2) / (sin α ^ 2 * cos α ^ 2 * sin β ^ 2 * cos β ^ 2) := by
      field_simp
      <;> ring
      <;> field_simp
      <;> ring
      <;> field_simp
      <;> ring
    rw [h17]
    apply div_nonneg
    nlinarith [sq_nonneg (sin α ^ 2 - 1 / 3), sq_nonneg (sin β ^ 2 * cos β ^ 2 - 1 / 4), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, mul_pos h5 h6, mul_pos h7 h8, h11, h10]

    all_goals positivity

  linarith