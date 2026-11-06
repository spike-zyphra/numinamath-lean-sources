import Mathlib

open Real Set

theorem inequalities_2927
  (x y : ℝ)
  (hx : x ∈ Icc 0 1)
  (hy : y ∈ Icc 0 1) :
  (1 - x * y) ^ 2 ≥ 4 * (x - y^2) * (y - x^2) := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y), sq_nonneg (x * y - x / 2 - y / 2), 
    sq_nonneg (x ^ 2 + y ^ 2 - x * y), sq_nonneg (x - y), sq_nonneg (x + y - 1), mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr hx1), 
    mul_nonneg (sub_nonneg.mpr hy0) (sub_nonneg.mpr hy1), 
    mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr hy0), 
    mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr hy1), 
    mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy0), 
    mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1)]