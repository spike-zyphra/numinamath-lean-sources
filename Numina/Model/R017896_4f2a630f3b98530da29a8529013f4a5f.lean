import Mathlib

theorem algebra_293027 (x y z : ℝ) (h₀ : x + y + z = 2) (h₁ : x * y + y * z + z * x = 1) :
    x - y ≤ 2 / Real.sqrt 3 ∧ ∃ x y z, x + y + z = 2 ∧ x * y + y * z + z * x = 1 ∧ x - y = 2 / Real.sqrt 3 := by
  have h2 : z = 2 - x - y := by linarith
  rw [h2] at h₁
  have h3 : 3 * (x + y) ^ 2 - 8 * (x + y) + 4 + (x - y) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 4 / 3)]
  have h4 : (x - y) ^ 2 ≤ 4 / 3 := by
    nlinarith [sq_nonneg (3 * (x + y) - 4), sq_nonneg (x - y), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h5 : x - y ≤ 2 / Real.sqrt 3 := by
    have h6 : (x - y) ^ 2 ≤ (4 / 3) := h4
    have h7 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num : 0 < (3 : ℝ))
    have h8 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))
    have h9 : Real.sqrt 3 * (x - y) ≤ 2 := by
      nlinarith [ sq_nonneg (Real.sqrt 3 * (x - y) - 2), Real.sqrt_nonneg 3, sq_nonneg (x - y - (2 / Real.sqrt 3)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h6, sq_nonneg (Real.sqrt 3), Real.sqrt_nonneg 3 ]
    have h10 : x - y ≤ (2 / Real.sqrt 3) := by
      have h11 : 0 < Real.sqrt 3 := h7
      apply (le_div_iff₀ h11).mpr
      nlinarith
    linarith
  constructor
  · exact h5
  · -- Show existence.
    use (2 + Real.sqrt 3) / 3, (2 - Real.sqrt 3) / 3, 2/3
    constructor
    · -- Show x + y + z = 2
      field_simp
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    constructor
    · -- Show x * y + y * z + z * x = 1
      field_simp
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- Show x - y = 2 / Real.sqrt 3
      have h11 : ((2 + Real.sqrt 3) / 3 : ℝ) - ((2 - Real.sqrt 3) / 3 : ℝ) = 2 / Real.sqrt 3 := by
        field_simp
        <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      linarith [h11]