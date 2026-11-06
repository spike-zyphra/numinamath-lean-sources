import Mathlib

theorem algebra_277387 {a b c : ℝ} (h : ∃ d, b = a + d ∧ c = b + d) :
    3 * (a ^ 2 + b ^ 2 + c ^ 2) = 6 * (a - b) ^ 2 + (a + b + c) ^ 2 := by 
        rcases h with ⟨d, hb, hc⟩ 
        have hc2 : c = a + 2 * d := by 
            linarith [hb, hc] 
        rw [hb, hc2] 
        nlinarith [sq_nonneg (a + d), sq_nonneg (d)]