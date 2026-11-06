import Mathlib
open Real Set
open scoped BigOperators

theorem algebra_8375 {a : ℝ} (hf : ∀ x ∈ Icc (-1) (1/2), |a*x^3-6*x| ≤ 2) :
    ∀ x ∈ Icc (-3/2) (3/2), |a*x^3-6*x| ≤ 18 := by
  have h1 := hf (-1) (left_mem_Icc.2 (by norm_num))
  have h2 := hf (1 / 2) (by norm_num [mem_Icc])
  have h4 : 4 ≤ a ∧ a ≤ 8 := by
    have h5 : -2 ≤ a * (-1) ^ 3 - 6 * (-1) := by linarith [abs_le.mp h1]
    have h6 : a * (-1) ^ 3 - 6 * (-1) ≤ 2 := by linarith [abs_le.mp h1]
    have h7 : -2 ≤ a * (1/2 )^3 - 6 * (1/2 ) := by linarith [abs_le.mp h2]
    have h8 : a * (1/2 )^3 - 6 * (1/2 ) ≤ 2 := by linarith [abs_le.mp h2]
    norm_num at h5 h6 h7 h8
    constructor
    linarith
    linarith
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  have h5 := h4.1
  have h6 := h4.2
  have h7 : -18 ≤ a * x ^ 3 - 6 * x := by
    nlinarith [sq_nonneg (x + 3 / 2), sq_nonneg (x - 3 / 2), sq_nonneg (x * (x - 3 / 2)), sq_nonneg (x * (x + 3 / 2)), sq_nonneg (a - 4), sq_nonneg (a - 8)]
  have h8 : a * x ^ 3 - 6 * x ≤ 18 := by
    nlinarith [sq_nonneg (x + 3 / 2), sq_nonneg (x - 3 / 2), sq_nonneg (x * (x - 3 / 2)), sq_nonneg (x * (x + 3 / 2)), sq_nonneg (a - 4), sq_nonneg (a - 8)]
  apply abs_le.mpr
  constructor <;> linarith