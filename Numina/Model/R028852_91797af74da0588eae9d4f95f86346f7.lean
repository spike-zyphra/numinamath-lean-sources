import Mathlib

theorem algebra_302352 (a : ℝ) (h : ∃ x ∈ Set.Icc (-1) 1, x^2 - 4 * x + 3 * a^2 - 2 = 0) :
    -Real.sqrt 15 / 3 ≤ a ∧ a ≤ Real.sqrt 15 / 3 := by
  rcases h with ⟨x, hx, heq⟩
  rw [Set.mem_Icc] at hx
  rcases hx with ⟨hx1, hx2⟩
  have h3 : -3 ≤ x ^ 2 - 4 * x ∧ x ^ 2 - 4 * x ≤ 5 := by
    constructor
    · -- Show -3 ≤ x^2 -4*x
      nlinarith [sq_nonneg (x - 2)]
    · -- Show x^2 -4*x ≤ 5
      nlinarith [sq_nonneg (x - 2)]
  have h4 : -3 ≤ -3 * a ^ 2 + 2 := by
    nlinarith [heq, h3.1]
  have h5 : a^2 ≤ 5 / 3 := by
    nlinarith
  have h6 : -Real.sqrt 15 / 3 ≤ a := by
    have h7 : a ^ 2 ≤ 5 / 3 := h5
    have h8 : Real.sqrt 15 ^ 2 = 15 := by
      rw [Real.sq_sqrt]
      norm_num
    nlinarith [Real.sqrt_nonneg 15, Real.sqrt_nonneg 15, Real.sq_sqrt (show 0 ≤ (15 : ℝ) by norm_num)]
  have h7 : a ≤ Real.sqrt 15 / 3 := by
    have h7 : a ^ 2 ≤ 5 / 3 := h5
    have h8 : Real.sqrt 15 ^ 2 = 15 := by
      rw [Real.sq_sqrt]
      norm_num
    nlinarith [Real.sqrt_nonneg 15, Real.sqrt_nonneg 15, Real.sq_sqrt (show 0 ≤ (15 : ℝ) by norm_num)]
  constructor
  · exact h6
  · exact h7