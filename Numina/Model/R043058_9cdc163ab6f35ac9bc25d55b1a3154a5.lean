import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_8424 {a : ℝ} (hf : ∀ x ∈ Icc (-1) (1/2), |a*x^3 - 6*x| ≤ 2) :
    ∀ x ∈ Icc (-3/2) (3/2), |a*x^3 - 6*x| ≤ 18 := by
  have h1 := hf (-1) (by norm_num)
  have h2 := hf (1/2) (by norm_num)
  have h3 : -2 ≤ a * (-1) ^ 3 - 6 * (-1) := by
    linarith [abs_le.mp h1]
  have h4 : a * (-1) ^ 3 - 6 * (-1) ≤ 2 := by
    linarith [abs_le.mp h1]
  have h5 : -2 ≤ a * (1/2) ^ 3 - 6 * (1/2) := by
    linarith [abs_le.mp h2]
  have h6 : a * (1/2) ^ 3 - 6 * (1/2) ≤ 2 := by
    linarith [abs_le.mp h2]
  have ha : a = 8 := by
    nlinarith
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  rw [ha]
  have hx3 : -3/2 ≤ x := hx1
  have hx4 : x ≤ 3/2 := hx2
  have h7 : -18 ≤ (8 * x ^ 3 - 6 * x) := by
    nlinarith [sq_nonneg (x + 3/2), sq_nonneg (x - 3/2), sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 1)]
  have h8 : (8 * x ^ 3 - 6 * x) ≤ 18 := by
    nlinarith [sq_nonneg (x + 3/2), sq_nonneg (x - 3/2), sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 1)]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (x + 3/2), sq_nonneg (x - 3/2), sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 1)]