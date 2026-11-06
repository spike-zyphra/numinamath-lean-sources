import Mathlib

theorem algebra_9795 (f : ℝ → ℝ) (hf : f = λ x => -7 / (x ^ 2 + 42 * x + 882)) :
  IsLeast {y | ∃ x, y = f x ∧ x < 0} (-1 / 63) := by
  constructor
  · -- Show that -1/63 is in the set
    use -21
    constructor
    · -- Show that f(-21) = -1/63
      rw [hf]
      norm_num
    · -- Show that -21 < 0
      norm_num
  · -- Show that -1/63 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx1, hx2⟩
    rw [hf] at hx1
    have h5 : (x ^ 2 + 42 * x + 882) > 0 := by
      nlinarith [sq_nonneg (x + 21)]
    have h4 : -7 / (x ^ 2 + 42 * x + 882) ≥ -1 / 63 := by
      have h5 : (x ^ 2 + 42 * x + 882) > 0 := by
        nlinarith [sq_nonneg (x + 21)]
      have h6 : x ^ 2 + 42 * x + 882 ≥ 441 := by
        nlinarith [sq_nonneg (x + 21)]
      have h8 : -7 / (x ^ 2 + 42 * x + 882) + (1 / 63 : ℝ) ≥ 0 := by 
        have h9 : (x + 21) ^ 2 ≥ 0 := by nlinarith [sq_nonneg (x + 21)]
        have h10 : x ^ 2 + 42 * x + 441 ≥ 0 := by
          nlinarith [sq_nonneg (x + 21)]
        have h11 : (-7 / (x ^ 2 + 42 * x + 882) : ℝ) + (1 / 63 : ℝ) =
          ((x ^ 2 + 42 * x + 441) : ℝ) / ((63 : ℝ) * (x ^ 2 + 42 * x + 882)) := by 
          field_simp [(show (x ^ 2 + 42 * x + 882) ≠ 0 by linarith [h5])]
          ring
        rw [h11]
        apply div_nonneg
        linarith [h10]
        all_goals nlinarith [h5]
      linarith
    have : y ≥ -1 / 63 := by 
      simp [hx1] at *
      linarith [h4]
    linarith