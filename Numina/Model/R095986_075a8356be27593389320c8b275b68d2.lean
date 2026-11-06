import Mathlib

open Real
open scoped BigOperators

theorem inequalities_250525 (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    x / (1 + y) + y / (1 + x) ≤ 1 := by

  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  have h1 : 0 ≤ 1 + y := by linarith
  have h2 : 0 ≤ 1 + x := by linarith
  have h3 : x / (1 + y) + y / (1 + x) - 1 ≤ 0 := by
    have h4 : x / (1 + y) + y / (1 + x) - 1 = (x ^ 2 + y ^ 2 - 1 - x * y) / ((1 + y) * (1 + x)) := by
      field_simp
      ring
    rw [h4]
    have h5 : (x ^ 2 + y ^ 2 - 1 - x * y) ≤ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1),
          mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr hy0),
          mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1)]
    have h6 : (1 + y) * (1 + x) > 0 := by positivity
    exact div_nonpos_of_nonpos_of_nonneg h5 (show (1 + y) * (1 + x) ≥ 0 by positivity)
  linarith