import Mathlib

theorem algebra_302967 {a b c : ℝ} (ha : a > 0) (h : b > a + c) :
    ∃ x y, x ≠ y ∧ a * x ^ 2 + b * x + c = 0 ∧ a * y ^ 2 + b * y + c = 0 := by
  have h1 : b ^ 2 - 4 * a * c > 0 := by
    nlinarith [sq_pos_of_pos ha, sq_nonneg (b - (a + c)), sq_nonneg (a - c), sq_nonneg (b + a + c), sq_nonneg (b - (a + c)), sq_pos_of_pos (show a > 0 by linarith), mul_pos ha (show a > 0 by linarith), sq_nonneg (a), sq_nonneg (b - c)]
  
  use (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a),
    (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
  
  constructor
  · -- Show that x ≠ y.
    by_contra h_eq
    have h2 : (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by
      linarith [h_eq]
    
    have h3 : (-b + Real.sqrt (b ^ 2 - 4 * a * c)) = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) := by
      field_simp [(show 2 * a ≠ 0 by nlinarith)] at h2 ⊢
      <;> nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c), Real.sqrt_nonneg (b ^ 2 - 4 * a * c)]
    
    have h4 : Real.sqrt (b ^ 2 - 4 * a * c) = 0 := by
      nlinarith [h3, Real.sqrt_nonneg (b ^ 2 - 4 * a * c)]
    
    have h5 : Real.sqrt (b ^ 2 - 4 * a * c) > 0 := by
      apply Real.sqrt_pos.mpr
      nlinarith

    linarith [h4, Real.sqrt_nonneg (b ^ 2 - 4 * a * c), h5]
  
  constructor
  · -- Show that a * x^2 + b * x + c = 0.
    field_simp [(show 2 * a ≠ 0 by nlinarith)]
    ring_nf
    rw [Real.sq_sqrt (by nlinarith)]
    <;> nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c), Real.sqrt_nonneg (b ^ 2 - 4 * a * c), sq_nonneg (b + 2 * a), sq_nonneg (c - a), h1]
  
  · -- Show that a * y^2 + b * y + c = 0.
    field_simp [(show 2 * a ≠ 0 by nlinarith)]
    ring_nf
    rw [Real.sq_sqrt (by nlinarith)]
    <;> nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * a * c), Real.sqrt_nonneg (b ^ 2 - 4 * a * c), sq_nonneg (b + 2 * a), sq_nonneg (c - a), h1]