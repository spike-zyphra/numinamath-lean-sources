import Mathlib

open Real Set
open scoped Real

theorem algebra_150600 (α β : ℝ) (h : sin (α + β) / sin (α - β) = 3) :
    tan α / tan β = 2 := by

  have h1 : sin (α - β) ≠ 0 := by
    by_contra h1
    have : sin (α + β) / sin (α - β) = 0 := by
      rw [h1]
      norm_num
    linarith [h, this]

  have h2 : sin (α + β) = 3 * sin (α - β) := by
    have h1' : sin (α - β) ≠ 0 := h1
    field_simp [h1'] at h ⊢
    linarith

  have h3 : sin (α + β) = sin α * cos β + cos α * sin β := by
    rw [sin_add]

  have h4 : sin (α - β) = sin α * cos β - cos α * sin β := by 
    rw [sin_sub]

  rw [h3] at h2
  rw [h4] at h2

  have h5 : 2 * cos α * sin β = sin α * cos β := by
    nlinarith

  have htan : tan α / tan β = (sin α * cos β) / (cos α * sin β) := by
    field_simp [tan_eq_sin_div_cos]

  rw [htan]

  have h7 : cos α * sin β ≠ 0 := by 
    by_contra h7
    have h8 : cos α * sin β = 0 := by 
      nlinarith

    have h9 : sin α * cos β = 0 := by
      nlinarith [h5, h8]

    have h11 : sin (α + β) = 0 := by 
      rw [h3]
      nlinarith

    have h12 : sin (α - β) = 0 := by 
      rw [h4]
      nlinarith

    have h13 : sin (α + β) / sin (α - β) = 0 := by
      rw [h12]
      norm_num

    linarith [h, h13]

  have h6 : sin α * cos β = 2 * (cos α * sin β) := by 
    linarith [h5]

  have h8 : (sin α * cos β) / (cos α * sin β) = 2 := by
    have h9 : cos α * sin β ≠ 0 := h7
    have h10 : sin α * cos β = 2 * (cos α * sin β) := by 
      linarith [h5]

    have h11 : (sin α * cos β) / (cos α * sin β) = 2 := by
      have h12 : cos α * sin β ≠ 0 := h7
      have h13 : cos α ≠ 0 := by
        by_contra hcos
        have : cos α * sin β = 0 := by
          rw [hcos]
          ring
        contradiction

      have h14 : sin β ≠ 0 := by
        by_contra hsin
        have : cos α * sin β = 0 := by
          rw [hsin]
          ring
        contradiction

      field_simp [h13, h14] at *
      <;> nlinarith

    exact h11

  exact h8