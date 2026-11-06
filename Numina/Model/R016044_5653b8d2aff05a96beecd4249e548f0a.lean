import Mathlib

open Real

theorem inequalities_30350 {a b : ℝ} (hab : a < b) :
    a^3 - 3 * a ≤ b^3 - 3 * b + 4 ∧ ((a, b) = (-1, 1) ↔ a^3 - 3 * a = b^3 - 3 * b + 4) := by
  constructor
  · -- First part: prove that $a < b$ implies $ a^3 - 3 * a \leq b^3 - 3 * b + 4 $
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + 1), sq_nonneg (b - 1),
      sq_nonneg (a - 1), sq_nonneg (b + 1), sq_nonneg (a - b + 2), sq_nonneg (a + b - 0), sq_nonneg (a + 1 - (b - 1)), sq_nonneg (a - 1 + b), sq_nonneg (a - (-1)), sq_nonneg (b - 1),
      mul_pos (sub_pos_of_lt hab) (show (0 : ℝ) < 1 by norm_num), sq_nonneg (a ^ 2 - b ^ 2)]
  · -- Second part: prove when equality occurs
    constructor
    · -- Forward: If (a, b) = (-1, 1), then a^3 - 3 * a = b^3 - 3 * b + 4
      rintro ⟨rfl, rfl⟩
      norm_num
    · -- Backward: If a^3 - 3 * a = b^3 - 3 * b + 4, then (a, b) = (-1, 1)
      intro h_eq
      have h_eq2 : a^3 - 3 * a = b^3 - 3 * b + 4 := by
        linarith [h_eq]
      have eq1 : (a - b) * (a^2 + a * b + b^2 - 3) = 4 := by
        nlinarith [h_eq2]
      have h1 : a - b < 0 := by linarith 
      have h2 : a^2 + a * b + b^2 - 3 < 0 := by 
        nlinarith [eq1, h1]
      have h3 : (a + 1) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + 1), sq_nonneg (b - 1), sq_nonneg (a - 1), sq_nonneg (b + 1), sq_nonneg (a + 1 - (b - 1)), sq_nonneg (a - b), sq_nonneg (a + 1 + (b - 1)), sq_nonneg (a - 1 + (b + 1)), h1, h2, mul_pos (sub_pos_of_lt hab) (show (0 : ℝ) < 1 by norm_num)]
      have h4 : a + 1 = 0 := by 
        nlinarith [h3]
      have ha2 : a = -1 := by 
        linarith 
      have h5 : (b - 1) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + 1), sq_nonneg (b - 1), sq_nonneg (a - 1), sq_nonneg (b + 1), sq_nonneg (a + 1 - (b - 1)), sq_nonneg (a - b), sq_nonneg (a + 1 + (b - 1)), sq_nonneg (a - 1 + (b + 1)), h1, h2, mul_pos (sub_pos_of_lt hab) (show (0 : ℝ) < 1 by norm_num)]
      have h6 : b - 1 = 0 := by 
        nlinarith [h5]
      have hb2 : b = 1 := by 
        linarith 
      simp [Prod.ext_iff, ha2, hb2]