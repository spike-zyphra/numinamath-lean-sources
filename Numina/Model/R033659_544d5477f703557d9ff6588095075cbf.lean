import Mathlib

theorem algebra_4299 (m : ℝ) (x₁ x₂ : ℝ)
    (h₁ : x₁^2 - 2*(m-1)*x₁ + m^2 + 3 = 0)
    (h₂ : x₂^2 - 2*(m-1)*x₂ + m^2 + 3 = 0)
    (h₃ : abs x₁ - 4 ≥ -abs x₂) :
    m ≤ -1 := by
  have h4 : abs x₁ + abs x₂ ≥ 4 := by
    linarith [abs_nonneg x₁, abs_nonneg x₂, h₃]
  cases' abs_cases x₁ with h1 h1 <;> cases' abs_cases x₂ with h2 h2 <;> 
    try { nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - 2 * (m - 1)), sq_nonneg (m + 1), sq_nonneg (x₁ - (m - 1)), sq_nonneg (x₂ - (m - 1)), sq_nonneg (x₁ + x₂), sq_nonneg (x₁ * x₂ - (m^2 + 3)), sq_nonneg (x₁ - x₂)] }
  all_goals 
    try { 
      nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - 2 * (m - 1)), sq_nonneg (m + 1), sq_nonneg (x₁ - (m - 1)), sq_nonneg (x₂ - (m - 1)), sq_nonneg (x₁ + x₂), sq_nonneg (x₁ * x₂ - (m^2 + 3)), sq_nonneg (x₁ - x₂)]
    }