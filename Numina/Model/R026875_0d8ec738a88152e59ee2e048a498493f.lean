import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_7215 (x y : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) + 1 / 2 ≥ 2 / (1 + 2 * x * y) := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  have h1 : 0 ≤ x := hx0
  have h2 : x ≤ 1 := hx1
  have h3 : 0 ≤ y := hy0
  have h4 : y ≤ 1 := hy1
  have h5 : 0 ≤ x * y := mul_nonneg h1 h3
  have h6 : x * y ≤ 1 := by
    nlinarith
  have h7 : 0 ≤ 2 * x * y := by linarith
  have h8 : 2 * x * y ≤ 2 := by
    nlinarith
  have h9 : 1 ≤ 1 + 2 * x * y := by linarith
  have h10 : 1 + 2 * x * y ≤ 3 := by linarith
  have h11 : 1 ≤ 1 + x ^ 2 := by nlinarith
  have h12 : 1 + x ^ 2 ≤ 2 := by nlinarith [sq_nonneg (x - 1)]
  have h13 : 1 ≤ 1 + y ^ 2 := by nlinarith
  have h14 : 1 + y ^ 2 ≤ 2 := by nlinarith [sq_nonneg (y - 1)]
  have h15 : 0 < (1 + x ^ 2) * (1 + y ^ 2) * (1 + 2 * x * y) := by
    positivity
  have h16 : (1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) + 1 / 2) - (2 / (1 + 2 * x * y)) ≥ 0 := by
    have h17 : (1 / (1 + x ^ 2) + 1 / (1 + y ^ 2) + 1 / 2) - (2 / (1 + 2 * x * y)) =
        (2 * (1 + y^2) * (1 + 2 * x * y) + 2 * (1 + x^2) * (1 + 2 * x * y) + (1 + x^2) * (1 + y^2) * (1 + 2 * x * y) - 4 * (1 + x^2) * (1 + y^2)) / (2 * (1 + x^2) * (1 + y^2) * (1 + 2 * x * y)) := by
      field_simp
      ring
    rw [h17]
    have h18 : 2 * (1 + x^2) * (1 + y^2) * (1 + 2 * x * y) > 0 := by positivity
    have h19 : 2 * (1 + y^2) * (1 + 2 * x * y) + 2 * (1 + x^2) * (1 + 2 * x * y) + (1 + x^2) * (1 + y^2) * (1 + 2 * x * y) - 4 * (1 + x^2) * (1 + y^2) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 1 / 2), sq_nonneg (x - 1/2), sq_nonneg (y - 1/2), 
        mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr hy0), 
        mul_nonneg (sub_nonneg.mpr (by linarith : 0 ≤ 1 - x)) (sub_nonneg.mpr (by linarith : 0 ≤ 1 - y)), 
        mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr (by linarith : 0 ≤ 1 - x)), 
        mul_nonneg (sub_nonneg.mpr hy0) (sub_nonneg.mpr (by linarith : 0 ≤ 1 - y)), 
        sq_nonneg (x * y - 1 / 2), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]
    apply div_nonneg 
    linarith 
    all_goals positivity
  linarith