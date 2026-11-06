import Mathlib

theorem number_theory_196664 {c : ℕ} (h : 111111222222 = c * (c + 1)) : c = 333333 := by
  have h1 : c ≤ 333333 := by
    nlinarith
  have h2 : c = 333333 := by
    nlinarith [h, h1]
  exact h2