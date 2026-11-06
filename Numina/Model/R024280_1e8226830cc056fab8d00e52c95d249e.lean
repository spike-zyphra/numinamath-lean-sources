import Mathlib

theorem algebra_313586 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    1 < (x * y + x + y) * (x + y + 1) / ((x + y) * (x + 1) * (y + 1)) ∧
    (x * y + x + y) * (x + y + 1) / ((x + y) * (x + 1) * (y + 1)) ≤ 9 / 8 := by

  have h1 : 0 < (x + y) * (x + 1) * (y + 1) := by
    positivity
  constructor
  · -- Show that 1 < (x * y + x + y) * (x + y + 1) / ((x + y) * (x + 1) * (y + 1))
    have h2 : (x * y + x + y) * (x + y + 1) / ((x + y) * (x + 1) * (y + 1)) > 1 := by
      have h2 : (x * y + x + y) * (x + y + 1) > (x + y) * (x + 1) * (y + 1) := by
        nlinarith [mul_pos hx hy, sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + y - 1)]
      have h4 : 0 < (x + y) * (x + 1) * (y + 1) := h1
      have h3 : (x * y + x + y) * (x + y + 1) / ((x + y) * (x + 1) * (y + 1)) > 1 := by
        apply (lt_div_iff₀ (by positivity)).mpr
        linarith
      linarith
    linarith
    all_goals linarith
  · -- Show that (x * y + x + y) * (x + y + 1) / ((x + y) * (x + 1) * (y + 1)) ≤ 9 / 8
    have h3 : (x * y + x + y) * (x + y + 1) / ((x + y) * (x + 1) * (y + 1)) ≤ 9 / 8 := by
      have h4 : (x * y + x + y) * (x + y + 1) ≤ 9 / 8 * ((x + y) * (x + 1) * (y + 1)) := by
        nlinarith [mul_pos hx hy, sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x * y - 1), sq_nonneg (x + y - 2)]
      have h4' : 0 < (x + y) * (x + 1) * (y + 1) := h1
      have h5 : (x * y + x + y) * (x + y + 1) / ((x + y) * (x + 1) * (y + 1)) ≤ 9 / 8 := by
        apply (div_le_iff₀ (by positivity)).mpr
        linarith
      linarith
    linarith
    all_goals linarith
  all_goals linarith
  all_goals positivity