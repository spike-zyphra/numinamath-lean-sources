import Mathlib

theorem algebra_261964 :
  {(x, y) : ℝ × ℝ | 
    10 / (2 * x + 3 * y - 29) + 9 / (7 * x - 8 * y + 24) = 8 ∧
    (2 * x + 3 * y - 29) / 2 = (7 * x - 8 * y) / 3 + 8 ∧
    7 * x - 8 * y + 24 ≠ 0 ∧ 
    2 * x + 3 * y - 29 ≠ 0} = {(5, 7)} := by
  ext ⟨x, y⟩
  simp [-one_div]
  constructor
  · -- Assume (x, y) satisfies the system of equations and none of the denominators is zero
    rintro ⟨h1, h2, h3, h4⟩
    have eq3 : 3 * (2 * x + 3 * y - 29) = 2 * (7 * x - 8 * y) + 48 := by
      have h3' : (7 * x - 8 * y + 24 : ℝ) ≠ 0 := h3
      field_simp at h2 ⊢
      nlinarith [h3']
    have eq4 : 10 * (7 * x - 8 * y + 24) + 9 * (2 * x + 3 * y - 29) = 8 * (2 * x + 3 * y - 29) * (7 * x - 8 * y + 24) := by
      have h3' : (7 * x - 8 * y + 24 : ℝ) ≠ 0 := h3
      have h4' : (2 * x + 3 * y - 29 : ℝ) ≠ 0 := h4
      field_simp [h3', h4'] at h1 ⊢
      nlinarith
    have h5 : 7 * x - 8 * y + 24 = 3 := by
      nlinarith [sq_pos_of_ne_zero (show (7 * x - 8 * y + 24 : ℝ) ≠ 0 by assumption), sq_pos_of_ne_zero (show (2 * x + 3 * y - 29 : ℝ) ≠ 0 by assumption), sq_nonneg (7 * x - 8 * y + 24 - 3), sq_nonneg (2 * x + 3 * y - 29 - 2)]
    have h6 : 2 * x + 3 * y - 29 = 2 := by
      nlinarith [h5, sq_nonneg (2 * x + 3 * y - 29 - 2)]
    have hx : x = 5 := by
      nlinarith [h5, h6]
    have hy : y = 7 := by
      nlinarith [h5, h6]
    simp [hx, hy]
  · -- Show that (5,7) satisfies the system of equations
    rintro ⟨rfl, rfl⟩
    constructor
    · -- Check first equation
      norm_num
    constructor
    · -- Check second equation
      norm_num
    constructor
    · -- Check that 7x - 8y + 24 ≠ 0
      norm_num
    · -- Check that 2x + 3y - 29 ≠ 0
      norm_num