import Mathlib

theorem algebra_301506 (a b c d e f g h i j : ℝ)
    (h₀ : a * 1 + b * 1 + c * 1 = 1010000)
    (h₁ : a * 2 + b * 2 + c * 2 = 2040000)
    (h₂ : a * 3 + b * 3 + c * 3 = 3090000)
    (h₃ : d * 1 + e * 1 + f * 1 = 1000000)
    (h₄ : d * 2 + e * 2 + f * 2 = 1000000)
    (h₅ : d * 3 + e * 3 + f * 3 = 1000000)
    (h₆ : g * 1 + h * 1 + i * 1 = 700000 - 30000)
    (h₇ : g * 2 + h * 2 + i * 2 = 700000 - 50000)
    (h₈ : g * 3 + h * 3 + i * 3 = 700000 - 70000)
    (h₉ : g * 4 + h * 4 + i * 4 = 700000 - 90000)
    (h₁₀ : g * 5 + h * 5 + i * 5 = 700000 - 110000) :
    IsLeast {n | n ≥ 1 ∧ (a * n + b * n + c * n) > (d * n + e * n + f * n)} 9 := by
  -- Lean's proof from inconsistent hypotheses
  linarith