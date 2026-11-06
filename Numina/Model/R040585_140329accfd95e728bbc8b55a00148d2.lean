import Mathlib

theorem number_theory_310637 (x y : ℤ) (hx : 0 < x) (hy : 0 < y) :
    x^3 + y^3 ≠ 1987 := by
  rintro h
  have h1 : x^3 + y^3 = 1987 := h
  have h2 : x ≤ 12 := by
    by_contra h3
    push_neg at h3
    have h4 : x^3 ≥ 13^3 := by
      have h5 : x ≥ 13 := h3
      have h6 : x^3 ≥ 13^3 := by
        apply pow_le_pow_left
        all_goals nlinarith
      linarith
    have h7 : y^3 ≥ 1 := by
      have h8 : y ≥ 1 := by nlinarith
      have h9 : y^3 ≥ 1 := by
        nlinarith [sq_nonneg (y - 1)]
      linarith
    have h8 : x^3 + y^3 ≥ 13^3 + 1 := by
      linarith [h4, h7]
    norm_num at h8 h1
    all_goals linarith
  have h3 : y ≤ 12 := by
    by_contra h4
    push_neg at h4
    have h4 : y^3 ≥ 13^3 := by
      have h5 : y ≥ 13 := h4
      have h6 : y^3 ≥ 13^3 := by
        apply pow_le_pow_left
        all_goals nlinarith
      linarith
    have h7 : x^3 ≥ 1 := by
      have h8 : x ≥ 1 := by nlinarith
      have h9 : x^3 ≥ 1 := by
        nlinarith [sq_nonneg (x - 1)]
      linarith
    have h8 : x^3 + y^3 ≥ 13^3 + 1 := by
      linarith [h7, h4]
    norm_num at h8 h1
    all_goals linarith
  interval_cases x <;> interval_cases y
  <;> omega