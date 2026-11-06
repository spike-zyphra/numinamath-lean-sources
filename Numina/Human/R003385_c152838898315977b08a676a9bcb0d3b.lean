import Mathlib

theorem algebra_174839 (a b c d : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₂ : a + b = 1900 ∧ a + c = 2070 ∧ a + d = 2110 ∧ b + c = 2330 ∧ b + d = 2500) :
    c + d = 2290 := by linarith