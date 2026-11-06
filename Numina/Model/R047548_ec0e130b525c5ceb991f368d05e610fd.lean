import Mathlib

theorem inequalities_70123 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    2 / (x + y + 2) ≤ 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 := by
  have h1 : 0 < Real.sqrt x := by
    apply Real.sqrt_pos.mpr
    linarith
  have h2 : 0 < Real.sqrt y := by
    apply Real.sqrt_pos.mpr
    linarith
  have h3 : 0 < (1 + Real.sqrt x) := by
    linarith [Real.sqrt_nonneg x, Real.sqrt_pos.mpr hx]
  have h4 : 0 < (1 + Real.sqrt y) := by
    linarith [Real.sqrt_nonneg y, Real.sqrt_pos.mpr hy]
  have h5 : 0 < (1 + Real.sqrt x) ^ 2 := by positivity
  have h6 : 0 < (1 + Real.sqrt y) ^ 2 := by positivity
  have h7 : 0 < x + y + 2 := by
    linarith [hx, hy]

  have h8 : 1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 - 2 / (x + y + 2) ≥ 0 := by
    have h9 : 0 < (1 + Real.sqrt x) ^ 2 * (1 + Real.sqrt y) ^ 2 * (x + y + 2) := by positivity
    have h10 : (1 / (1 + Real.sqrt x) ^ 2 + 1 / (1 + Real.sqrt y) ^ 2 - 2 / (x + y + 2)) =
      ( (1 * (1 + Real.sqrt y) ^ 2 * (x + y + 2) + 1 * (1 + Real.sqrt x) ^ 2 * (x + y + 2) - 2 * (1 + Real.sqrt x) ^ 2 * (1 + Real.sqrt y) ^ 2 ) / ( (1 + Real.sqrt x) ^ 2 * (1 + Real.sqrt y) ^ 2 * (x + y + 2) ) ) := by
      field_simp
      <;> ring
    rw [h10] at *
    apply div_nonneg
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt y - 1),
              Real.sq_sqrt (show 0 ≤ x by linarith),
              Real.sq_sqrt (show 0 ≤ y by linarith),
              sq_nonneg (Real.sqrt x + Real.sqrt y - 2), sq_nonneg (Real.sqrt x + 1 - (Real.sqrt y + 1)),
              mul_pos hx hy, mul_pos hx (show 0 < Real.sqrt y by positivity),
              mul_pos (show 0 < Real.sqrt x by positivity) (show 0 < Real.sqrt y by positivity), Real.sqrt_nonneg x, Real.sqrt_nonneg y,
              mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
    positivity

  linarith [h8]