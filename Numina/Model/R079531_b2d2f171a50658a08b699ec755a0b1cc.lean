import Mathlib

theorem inequalities_86521 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) :
    (1 + 1 / x) * (1 + 1 / y) ≥ 9 := by

  have h1 : (1 + 1 / x) * (1 + 1 / y) = 1 + 2 / (x * y) := by
    field_simp
    <;> nlinarith [hxy]

  have h2 : x * y ≤ 1 / 4 := by
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), hxy]

  have h3 : 0 < x * y := by
    apply mul_pos
    all_goals linarith

  have h4 : 1 + 2 / (x * y) ≥ 9 := by
    have h5 : (x * y) ≤ 1 / 4 := h2
    have h6 : 0 < x * y := h3
    have h7 : 2 / (x * y) ≥ 8 := by
      have h8 : x * y ≤ 1 / 4 := h5
      have h9 : 0 < x * y := h6
      have h10 : 2 / (x * y) ≥ 8 := by
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith
      linarith
    linarith

  linarith [h1, h4]