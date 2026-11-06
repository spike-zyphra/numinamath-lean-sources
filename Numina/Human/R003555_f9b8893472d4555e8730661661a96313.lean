import Mathlib

theorem algebra_195340 (A B C : ℝ) (h₀ : A ∈ Set.Ioo 0 π)
    (h₁ : B ∈ Set.Ioo 0 π) (h₂ : C ∈ Set.Ioo 0 π) (h₃ : A + B + C = π)
    (h₄ : A * B * C = 2 * (A * C * B)) (h₅ : B * C = 2 * A * B) :
    A * B * C = π / 2 := by
        have h6 : A * B * C = 2 * (A * C * B) := h₄
        have h7 : A * B * C - (A * C * B) = 0 := by
            linarith
        have h8 : A * C * B = 0 := by
            linarith
        have h9 : A > 0 := h₀.left
        have h10 : A < π := h₀.right
        have h11 : B > 0 := h₁.left
        have h12 : B < π := h₁.right
        have h13 : C > 0 := h₂.left
        have h14 : C < π := h₂.right
        have h15 : A * C * B > 0 := by
            apply mul_pos
            apply mul_pos
            all_goals linarith
        linarith