import Mathlib

theorem algebra_195805 (p : ℝ → ℝ → ℝ)
    (h₀ : ∀ a b, p a b = 2 * a ^ 2 - 8 * a * b + 17 * b ^ 2 - 16 * a - 4 * b + 2044) :
    IsLeast {x | ∃ a b, x = p a b} 1976 ∧ ∃ a b, p a b = 1976 ∧ a = 8 ∧ b = 2 := by

  constructor
  · -- Show 1976 is the least value
    constructor
    · -- Show 1976 is in the range
      use 8, 2
      norm_num [h₀]
    · -- Show no smaller value exists
      intro x hx
      rcases hx with ⟨a, b, h_eq⟩
      have h1 : p a b = 2 * (a - 2 * b - 4) ^ 2 + 9 * (b - 2) ^ 2 + 1976 := by
        rw [h₀ a b]
        nlinarith [sq_nonneg (a - 2 * b - 4), sq_nonneg (b - 2)]
      have h2 : x = 2 * (a - 2 * b - 4) ^ 2 + 9 * (b - 2) ^ 2 + 1976 := by
        rw [h_eq]
        linarith [h1]
      have h3 : 2 * (a - 2 * b - 4) ^ 2 + 9 * (b - 2) ^ 2 ≥ 0 := by
        nlinarith [sq_nonneg (a - 2 * b - 4), sq_nonneg (b - 2)]
      linarith [h2, h3]

  · -- Show there exist a, b such that p a b = 1976 and a = 8, b = 2
    use 8, 2
    norm_num [h₀]