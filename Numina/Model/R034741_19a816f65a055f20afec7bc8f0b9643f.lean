import Mathlib

theorem inequalities_599320 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    2 / (x + y + 2) ≤ 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 := by

  have h1 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h2 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have h3 : Real.sqrt x > 0 := by
    apply Real.sqrt_pos.mpr
    exact hx
  have h4 : Real.sqrt y > 0 := by
    apply Real.sqrt_pos.mpr
    exact hy
  have h5 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
  have h6 : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (by linarith)

  have h7 : 0 < x + y + 2 := by nlinarith
  have h8 : 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 - 2 / (x + y + 2) ≥ 0 := by

    have h9 : 0 < (1 + Real.sqrt x) ^ 2 := by
      nlinarith [Real.sqrt_pos.mpr hx, Real.sqrt_nonneg x]
    have h10 : 0 < (1 + Real.sqrt y) ^ 2 := by
      nlinarith [Real.sqrt_pos.mpr hy, Real.sqrt_nonneg y]
    have h11 : 0 < x + y + 2 := by nlinarith

    have h12 : 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 - 2 / (x + y + 2) =
        ((1 + Real.sqrt y) ^ 2 * (x + y + 2) + (1 + Real.sqrt x) ^ 2 * (x + y + 2) - 2 * (1 + Real.sqrt x) ^ 2 * (1 + Real.sqrt y) ^ 2) / ((1 + Real.sqrt x) ^ 2 * (1 + Real.sqrt y) ^ 2 * (x + y + 2)) := by
      field_simp [h9, h10, h11]
      <;> ring

    rw [h12] at *
    apply div_nonneg
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt y - 1),
        Real.sqrt_nonneg x, Real.sqrt_nonneg y,
        sq_nonneg (x - y), sq_nonneg (Real.sqrt x ^ 2 - Real.sqrt y ^ 2),
        Real.sq_sqrt (show 0 ≤ x by linarith),
        Real.sq_sqrt (show 0 ≤ y by linarith),
        mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y),
        sq_nonneg (Real.sqrt x + Real.sqrt y - 2)]
    all_goals positivity
  linarith