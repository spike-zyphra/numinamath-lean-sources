import Mathlib

theorem algebra_283036 {a b c : ℝ} (h₀ : a ≠ b) (h₁ : b ≠ c) (h₂ : c ≠ a) :
    (a - b)^2 / ((b - c) * (c - a)) + (b - c)^2 / ((c - a) * (a - b)) +
    (c - a)^2 / ((a - b) * (b - c)) = 3 := by
        have h3 : a - b ≠ 0 := sub_ne_zero_of_ne h₀
        have h4 : b - c ≠ 0 := sub_ne_zero_of_ne h₁
        have h5 : c - a ≠ 0 := sub_ne_zero_of_ne h₂
        field_simp [(show b - c ≠ 0 by exact h4), (show c - a ≠ 0 by exact h5), (show a - b ≠ 0 by exact h3)]
        ring