import Mathlib

theorem algebra_103781 {a b c : ℝ} (ha : a ≠ 0) (h : 5 * a + b + 2 * c = 0)
    (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 2 + b * x + c) :
    ∃ x1 x2, x1 ≠ x2 ∧ f x1 = 0 ∧ f x2 = 0 := by
  have h2 : c = (-5 * a - b) / 2 := by
    linarith

  have h1 : b ^ 2 - 4 * a * c > 0 := by
    rw [show c = (-5 * a - b) / 2 by linarith]
    have h6 : a ^ 2 > 0 := by
      apply sq_pos_of_ne_zero 
      exact ha
    nlinarith [sq_nonneg (b + a), sq_nonneg (b - a), sq_nonneg (b + 5 * a), sq_pos_of_ne_zero ha, sq_nonneg (b ^ 2), sq_nonneg ((-4 * a) * c), sq_nonneg (2 * a * b), sq_nonneg (b), sq_nonneg (c), sq_nonneg (b + 5*a), sq_nonneg (b - 5*a)]

  let x1 := (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
  let x2 := (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)

  use x1, x2

  constructor
  · -- Show that x₁ ≠ x₂
    by_contra h_eq
    have h_eq2 : (-b + Real.sqrt (b ^ 2 - 4 * a * c)) = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) := by
      have hne : 2 * a ≠ 0 := by 
        exact mul_ne_zero (by norm_num) ha
      have : (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by linarith [h_eq]
      have : (-b + Real.sqrt (b ^ 2 - 4 * a * c)) = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) := by
        field_simp [hne] at this ⊢
        <;> nlinarith
      assumption

    have h_zero : Real.sqrt (b ^ 2 - 4 * a * c) = 0 := by
      nlinarith [h_eq2, Real.sqrt_nonneg (b ^ 2 - 4 * a * c)]

    have h_zero' : (b ^ 2 - 4 * a * c) = 0 := by
      rw [Real.sqrt_eq_zero (by nlinarith)] at h_zero 
      linarith

    nlinarith

  constructor
  · -- Show f x1 = 0
    rw [hf]
    have hne : 2 * a ≠ 0 := by exact mul_ne_zero (by norm_num) ha
    have eq1 : a * x1 ^ 2 + b * x1 + c = 0 := by
      rw [show x1 = (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) by rfl]
      field_simp [hne]
      nlinarith [Real.sqrt_pos.mpr (show (b ^ 2 - 4 * a * c) > 0 by linarith), Real.sq_sqrt (show 0 ≤ (b ^ 2 - 4 * a * c : ℝ) by nlinarith), sq_pos_of_ne_zero ha, sq_nonneg (b), sq_nonneg (c), sq_nonneg (a), sq_nonneg (b * c), sq_nonneg ((b) ^ 2), sq_nonneg ((b * a)), sq_nonneg ((c * a))]
    assumption

  · -- Show f x2 = 0
    rw [hf]
    have hne : 2 * a ≠ 0 := by exact mul_ne_zero (by norm_num) ha
    have eq1 : a * x2 ^ 2 + b * x2 + c = 0 := by
      rw [show x2 = (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) by rfl]
      field_simp [hne]
      nlinarith [Real.sqrt_pos.mpr (show (b ^ 2 - 4 * a * c) > 0 by linarith), Real.sq_sqrt (show 0 ≤ (b ^ 2 - 4 * a * c : ℝ) by nlinarith), sq_pos_of_ne_zero ha, sq_nonneg (b), sq_nonneg (c), sq_nonneg (a), sq_nonneg (b * c), sq_nonneg ((b) ^ 2), sq_nonneg ((b * a)), sq_nonneg ((c * a))]
    assumption