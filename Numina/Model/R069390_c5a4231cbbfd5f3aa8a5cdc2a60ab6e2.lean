import Mathlib.Tactic

theorem inequalities_603704
(a b c : ℝ)
(h₀ : 0 ≤ a)
(h₁ : 0 ≤ b)
(h₂ : 0 ≤ c) :
(a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≥ 9 * (a * b + b * c + c * a) := by 
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b * c - 1),
          mul_nonneg h₀ h₁, mul_nonneg h₁ h₂, mul_nonneg h₂ h₀]