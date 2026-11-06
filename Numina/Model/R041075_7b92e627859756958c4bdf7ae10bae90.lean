import Mathlib

open Real

theorem algebra_167936 (α β : ℝ) (h₀ : sin α ^ 4 / sin β ^ 2 + cos α ^ 4 / cos β ^ 2 = 1)
    (h₁ : sin α * cos α * sin β * cos β ≠ 0) :
    sin β ^ 4 / sin α ^ 2 + cos β ^ 4 / cos α ^ 2 = 1 := by 
  have h2 : sin α ≠ 0 := by
    by_contra h
    have : sin α * cos α * sin β * cos β = 0 := by
      rw [h]
      norm_num
    contradiction
  have h3 : cos α ≠ 0 := by
    by_contra h
    have : sin α * cos α * sin β * cos β = 0 := by
      rw [h]
      norm_num
    contradiction
  have h4 : sin β ≠ 0 := by
    by_contra h
    have : sin α * cos α * sin β * cos β = 0 := by
      rw [h]
      norm_num
    contradiction
  have h5 : cos β ≠ 0 := by
    by_contra h
    have : sin α * cos α * sin β * cos β = 0 := by
      rw [h]
      norm_num
    contradiction
  have eq1 : sin α ^ 4 * cos β ^ 2 + cos α ^ 4 * sin β ^ 2 = sin β ^ 2 * cos β ^ 2 := by
    have eq1 : sin α ^ 4 / sin β ^ 2 + cos α ^ 4 / cos β ^ 2 = 1 := h₀
    have h6 : sin β ^ 2 * cos β ^ 2 ≠ 0 := by
      apply mul_ne_zero
      exact pow_ne_zero 2 h4
      exact pow_ne_zero 2 h5
    have eq2 : sin α ^ 4 / sin β ^ 2 + cos α ^ 4 / cos β ^ 2 =
        (sin α ^ 4 * cos β ^ 2 + cos α ^ 4 * sin β ^ 2) / (sin β ^ 2 * cos β ^ 2) := by
      field_simp [h4, h5]
      <;> ring
    rw [eq2] at eq1
    field_simp [h6] at eq1 ⊢
    linarith
  have h6 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h7 : sin β ^ 2 + cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  have h8 : sin β ^ 4 / sin α ^ 2 + cos β ^ 4 / cos α ^ 2 =
      (sin β ^ 4 * cos α ^ 2 + cos β ^ 4 * sin α ^ 2) / (sin α ^ 2 * cos α ^ 2) := by
    field_simp [h2, h3]
    <;> ring
  have h9 : sin α ^ 2 * cos α ^ 2 ≠ 0 := by
    apply mul_ne_zero
    exact pow_ne_zero 2 h2
    exact pow_ne_zero 2 h3
  rw [h8]
  have h10 : sin β ^ 4 * cos α ^ 2 + cos β ^ 4 * sin α ^ 2 = sin α ^ 2 * cos α ^ 2 := by
    have h11 : cos α ^ 2 = cos β ^ 2 := by
      have eq1' : sin α ^ 4 * cos β ^ 2 + cos α ^ 4 * sin β ^ 2 = sin β ^ 2 * cos β ^ 2 := eq1
      have h8 : sin α ^ 2 + cos α ^ 2 = 1 := h6
      have h9 : sin β ^ 2 + cos β ^ 2 = 1 := h7
      have h10 : sin α ^ 2 = 1 - cos α ^ 2 := by linarith
      have h11 : sin β ^ 2 = 1 - cos β ^ 2 := by linarith
      rw [show sin α ^ 4 = (sin α ^ 2) ^ 2 by ring, 
          show cos α ^ 4 = (cos α ^ 2) ^ 2 by ring, 
          h10, h11] at eq1'
      nlinarith [sq_nonneg (cos α ^ 2 - cos β ^ 2)]
    have h12 : sin α ^ 2 = sin β ^ 2 := by
      have h8' : sin α ^ 2 = 1 - cos α ^ 2 := by linarith [h6]
      have h9' : sin β ^ 2 = 1 - cos β ^ 2 := by linarith [h7]
      rw [h8', h9']
      linarith [h11]
    have h13 : sin β ^ 4 * cos α ^ 2 + cos β ^ 4 * sin α ^ 2 = sin α ^ 2 * cos α ^ 2 := by
      have h14 : sin β ^ 4 = (sin β ^ 2) ^ 2 := by ring
      have h15 : cos β ^ 4 = (cos β ^ 2) ^ 2 := by ring
      rw [h14, h15]
      have h17 : sin β ^ 2 = sin α ^ 2 := by nlinarith
      have h18 : cos β ^ 2 = cos α ^ 2 := by nlinarith
      rw [h17, h18]
      have h19 : (sin α ^ 2) ^ 2 * cos α ^ 2 + (cos α ^ 2) ^ 2 * sin α ^ 2 = 
          sin α ^ 2 * cos α ^ 2 := by 
        have h20 : sin α ^ 2 + cos α ^ 2 = 1 := h6
        nlinarith [sq_nonneg (sin α ^ 2 - cos α ^ 2)]
      linarith
    exact_mod_cast h13
  have h11 : (sin β ^ 4 * cos α ^ 2 + cos β ^ 4 * sin α ^ 2) / (sin α ^ 2 * cos α ^ 2) = 1 := by 
    rw [show sin β ^ 4 * cos α ^ 2 + cos β ^ 4 * sin α ^ 2 = 
      sin α ^ 2 * cos α ^ 2 by linarith [h10]]
    field_simp [h9]
    <;> linarith
  linarith [h11]