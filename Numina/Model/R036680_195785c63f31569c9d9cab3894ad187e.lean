import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_311555 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 - x + 1 + sqrt (2 * (x + 3)^2 + 2 * (x^2 - 5)^2)) :
  IsLeast (range f) 9 ∧
  ∃ x, f x = 9 := by
  have h1 : ∃ x, f x = 9 := by
    use -2
    rw [h₀]
    have h2 : sqrt (2 * (-2 + 3) ^ 2 + 2 * ((-2) ^ 2 - 5) ^ 2) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h2]
    norm_num
  have h2 : ∀ x, f x ≥ 9 := by
    intro x
    rw [h₀ x]
    have h4 : x ^ 2 - x + 1 + sqrt (2 * (x + 3) ^ 2 + 2 * (x ^ 2 - 5) ^ 2) ≥ 9 := by
      by_cases h : 9 - (x^2 -x + 1) ≥ 0
      · -- Assume that 9 - (x^2 -x +1) >= 0
        have h5 : sqrt (2 * (x + 3) ^ 2 + 2 * (x ^ 2 - 5) ^ 2) ≥ 9 - (x^2 - x + 1) := by
          have h6 : 2 * (x + 3) ^ 2 + 2 * (x ^ 2 - 5) ^ 2 ≥ (9 - (x^2 - x + 1)) ^ 2 := by
            nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 2), sq_nonneg (x^2 - 2), sq_nonneg (x - 1)]
          have h7 : sqrt (2 * (x + 3) ^ 2 + 2 * (x ^ 2 - 5) ^ 2) ≥ 0 := by positivity
          have h8 : (9 - (x^2 - x + 1)) ≥ 0 := h
          nlinarith [Real.sqrt_nonneg (2 * (x + 3) ^ 2 + 2 * (x ^ 2 - 5) ^ 2), Real.sq_sqrt (show 0 ≤ (2 * (x + 3) ^ 2 + 2 * (x ^ 2 - 5) ^ 2 : ℝ) by positivity)]
        nlinarith
      · -- Assume that 9 - (x^2 -x +1) < 0
        have h5 : sqrt (2 * (x + 3) ^ 2 + 2 * (x ^ 2 - 5) ^ 2) ≥ 9 - (x^2 - x + 1) := by
          have h9 : 9 - (x^2 - x + 1) < 0 := by linarith
          have h10 : sqrt (2 * (x + 3) ^ 2 + 2 * (x ^ 2 - 5) ^ 2) ≥ 0 := Real.sqrt_nonneg (2 * (x + 3) ^ 2 + 2 * (x ^ 2 - 5)  ^ 2)
          nlinarith
        nlinarith
    linarith
  constructor
  · -- Show that 9 is the minimum value of f
    constructor
    · -- Show that 9 is in the range of f
      exact h1
    · -- Show that 9 is the minimum
      intro y
      rintro ⟨x, hx⟩
      have h5 : f x ≥ 9 := h2 x
      linarith [hx, h5]
  · -- Show that ∃ x, f x = 9
    exact h1