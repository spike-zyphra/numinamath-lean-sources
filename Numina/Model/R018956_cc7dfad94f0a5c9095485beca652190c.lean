import Mathlib

theorem inequalities_297798 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 1) :
    (x + 1 / x) ^ 2 + (y + 1 / y) ^ 2 ≥ 25 / 2 := by
  have h2 : x * y ≤ 1 / 4 := by
    have h3 : x + y = 1 := hxy
    have h4 : (x + y) ^ 2 ≥ 4 * (x * y) := by
      nlinarith [sq_nonneg (x - y)]
    have h5 : (x + y) ^ 2 = 1 := by
      rw [h3]
      norm_num
    nlinarith
  have h3 : x * y > 0 := by
    apply mul_pos
    all_goals linarith
  have h4 : 1 / (x * y) ≥ 4 := by
    have h5 : x * y ≤ 1 / 4 := h2
    have h6 : x * y > 0 := h3
    have h7 : 1 - 4 * (x * y) ≥ 0 := by
      nlinarith
    have h9 : x * y > 0 := h3
    have h13 : (1 / (x * y) : ℝ) ≥ 4 := by
      apply (le_div_iff₀ (by nlinarith)).mpr
      nlinarith
    exact h13
  have h5 : 1 / x + 1 / y = 1 / (x * y) := by
    field_simp [(show x ≠ 0 by linarith), (show y ≠ 0 by linarith)]
    nlinarith [hxy]
  have h6 : 1 / x + 1 / y ≥ 4 := by
    linarith [h4, h5]
  have h7 : x + 1 / x + y + 1 / y ≥ 5 := by
    have h8 : x + y = 1 := hxy
    have h9 : x + y + (1 / x + 1 / y) = 1 + (1 / x + 1 / y) := by
      nlinarith [h8]
    nlinarith [h6, h9, sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), hxy]
  have h8 : (x + 1 / x) ^ 2 + (y + 1 / y) ^ 2 ≥ (x + 1 / x + (y + 1 / y)) ^ 2 / 2 := by
    linarith [sq_nonneg ((x + 1 / x) - (y + 1 / y))]
  have h9 : x + 1 / x + (y + 1 / y) = x + y + 1 / x + 1 / y := by
    ring
  have h10 : x + 1 / x + (y + 1 / y) ≥ 5 := by
    have h11 : x + 1 / x + (y + 1 / y) = x + y + 1 / x + 1 / y := by
      ring
    linarith [h7, h11]
  have h12 : (x + 1 / x + (y + 1 / y)) ^ 2 / 2 ≥ 25 / 2 := by
    have h13 : x + 1 / x + (y + 1 / y) ≥ 5 := h10
    nlinarith [sq_nonneg (x + 1 / x + (y + 1 / y) - 5)]
  linarith [h8, h12]