import Mathlib

theorem algebra_252554 (a b c : ℝ) (ha : 0 < a) (h : b > a + c) :
    ∃ x₁ x₂ : ℝ, x₁ ≠ x₂ ∧ a * x₁^2 + b * x₁ + c = 0 ∧ a * x₂^2 + b * x₂ + c = 0 := by
  have h1 : b ^ 2 - 4 * a * c > 0 := by
    nlinarith [sq_nonneg (b - (a + c)), sq_pos_of_pos ha, sq_nonneg (a - c)]
  use (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a),
    (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
  constructor
  · -- Show x₁ ≠ x₂
    by_contra h_eq
    have h_eq2 : (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by
      simpa using h_eq
    have h2 : (-b + Real.sqrt (b ^ 2 - 4 * a * c)) = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) := by
      field_simp [(show 0 < a by nlinarith)] at h_eq2 ⊢
      linarith
    have h3 : Real.sqrt (b ^ 2 - 4 * a * c) = 0 := by
      nlinarith [h2, Real.sqrt_nonneg (b ^ 2 - 4 * a * c)]
    have h4 : Real.sqrt (b ^ 2 - 4 * a * c) > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    linarith [h3, h4]
  constructor
  · -- Show the first root is a solution
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by nlinarith)]
    <;> nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c), sq_nonneg (Real.sqrt (b ^ 2 - 4 * a * c)), sq_nonneg (a)]
  · -- Show the second root is a solution
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by nlinarith)]
    <;> nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c), sq_nonneg (Real.sqrt (b ^ 2 - 4 * a * c)), sq_nonneg (a)]