import Mathlib

theorem algebra_114209 {a b c : ℝ} (h₀ : a^2 + 2 = b^4) (h₁ : b^2 + 2 = c^4)
    (h₂ : c^2 + 2 = a^4) :
    (a^2 - 1) * (b^2 - 1) * (c^2 - 1) = 1 := by
        have h7 : a^2 = 2 := by
            nlinarith [sq_nonneg (a^2 - 2), sq_nonneg (b^2 - 2), sq_nonneg (c^2 - 2),
                sq_nonneg (a^2 - c^2), sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2),
                h₀, h₁, h₂, sq_nonneg (a^2), sq_nonneg (b^2), sq_nonneg (c^2)]
        have h7' : b^2 = 2 := by
            nlinarith [sq_nonneg (a^2 - 2), sq_nonneg (b^2 - 2), sq_nonneg (c^2 - 2),
                sq_nonneg (a^2 - c^2), sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2),
                h₀, h₁, h₂, sq_nonneg (a^2), sq_nonneg (b^2), sq_nonneg (c^2)]
        have h7'' : c^2 = 2 := by
            nlinarith [sq_nonneg (a^2 - 2), sq_nonneg (b^2 - 2), sq_nonneg (c^2 - 2),
                sq_nonneg (a^2 - c^2), sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2),
                h₀, h₁, h₂, sq_nonneg (a^2), sq_nonneg (b^2), sq_nonneg (c^2)]
        rw [h7, h7', h7'']
        all_goals norm_num