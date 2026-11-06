import Mathlib

theorem algebra_317988 {a : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n) (h : a 2 + a 4 + a 6 + a 8 + a 10 = 80) :
    a 7 - (1 / 2) * a 8 = 8 := by
        rcases ha with ⟨d, had⟩
        have h2 : a 2 = a 0 + d * 2 := had 2
        have h4 : a 4 = a 0 + d * 4 := had 4
        have h6 : a 6 = a 0 + d * 6 := had 6
        have h8 : a 8 = a 0 + d * 8 := had 8
        have h10 : a 10 = a 0 + d * 10 := had 10
        rw [h2, h4, h6, h8, h10] at h
        have eq1 : 5 * a 0 + 30 * d = 80 := by
            linarith
        have eq2 : a 0 + 6 * d = 16 := by
            linarith
        have h7 : a 7 = a 0 + d * 7 := had 7
        have h8' : a 8 = a 0 + d * 8 := had 8
        rw [h7, h8']
        linarith [eq2]