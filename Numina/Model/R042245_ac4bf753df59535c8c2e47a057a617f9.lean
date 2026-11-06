import Mathlib
open Real

theorem algebra_9254 :
  IsLeast {y : ℝ | ∃ x, y = (x^2 + 5) / √(x^2 + 4)} (5 / 2) := by
  constructor
  · -- Show that 5/2 is in the set
    use 0
    have h1 : Real.sqrt (0 ^ 2 + 4) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    norm_num
  · -- Show that 5/2 is the least
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h2 : (x^2 + 5) / Real.sqrt (x^2 + 4) ≥ (5 / 2 : ℝ) := by
      have h3 : Real.sqrt (x^2 + 4) ≥ 0 := by positivity
      have h4 : Real.sqrt (x^2 + 4) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith [sq_nonneg x]
      have h6 : (x^2 + 5 : ℝ) ≥ (5 / 2 : ℝ) * Real.sqrt (x^2 + 4) := by
        nlinarith [Real.sqrt_nonneg (x^2 + 4), 
          Real.sq_sqrt (show x^2 + 4 ≥ 0 by positivity),
          sq_nonneg (Real.sqrt (x^2 + 4) - 2),
          sq_nonneg (x^2 - 1)
        ]
      have h7 : (x^2 + 5 : ℝ) ≥ (5 / 2 : ℝ) * Real.sqrt (x^2 + 4) := h6
      have h8 : (x^2 + 5 : ℝ) / Real.sqrt (x^2 + 4) ≥ (5 / 2 : ℝ) := by
        have h9 : Real.sqrt (x^2 + 4) > 0 := h4
        apply (le_div_iff₀ h9).mpr
        linarith [h7]
      linarith
    linarith [h2, hx]