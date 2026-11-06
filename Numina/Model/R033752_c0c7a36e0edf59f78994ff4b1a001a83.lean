import Mathlib

open Real Set

theorem inequalities_623016 :
    IsLeast {x | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a > b ∧ x = a ^ 2 + 1 / (b * (a - b))} 4 := by
  constructor
  · -- First part: show 4 is in the set
    use Real.sqrt 2, Real.sqrt 2 / 2
    constructor
    · -- Show a > 0
      positivity
    constructor
    · -- Show b > 0
      positivity
    constructor
    · -- Show a > b
      have h1 : Real.sqrt 2 > 0 := by positivity
      have h2 : Real.sqrt 2 > Real.sqrt 2 / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num : (2 : ℝ) > 0)]
      linarith
    · -- Show x = a^2 + 1/(b*(a - b))
      have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by linarith)
      field_simp [h3, show (Real.sqrt 2 - Real.sqrt 2 / 2) = Real.sqrt 2 / 2 by linarith, show Real.sqrt 2 * (Real.sqrt 2) = 2 by nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num : (2 : ℝ) > 0)]]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sqrt_nonneg 2]
  · -- Second part: show that 4 is minimal
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h1, hx⟩
    have h2 : a ^ 2 + 1 / (b * (a - b)) ≥ 4 := by
      have h3 : b * (a - b) > 0 := mul_pos hb (sub_pos.mpr h1)
      have h4 : a ^ 2 + 1 / (b * (a - b)) - 4 ≥ 0 := by
        have h5 : a ^ 2 + 1 / (b * (a - b)) - 4 = (a ^ 2 * (b * (a - b)) + 1 - 4 * (b * (a - b)) ) / (b * (a - b)) := by
          field_simp [show b * (a - b) ≠ 0 by nlinarith]
          <;> ring
        rw [h5]
        have h6 : b * (a - b) > 0 := h3
        have h7 : a ^ 2 * (b * (a - b)) + 1 - 4 * (b * (a - b)) ≥ 0 := by
          nlinarith [sq_nonneg (a ^ 2 - 2), sq_nonneg (b - a / 2), sq_nonneg (a * b - a * (a - b)), sq_nonneg (a * (a - b) - 1), sq_nonneg (a ^ 2 - 2), sq_nonneg ((b) - (a / 2)), mul_pos ha hb, mul_pos hb (show (0 : ℝ) < a - b by linarith)]
        apply div_nonneg 
        linarith
        linarith
      linarith
    linarith [show x = a ^ 2 + 1 / (b * (a - b)) by linarith [hx], h2]