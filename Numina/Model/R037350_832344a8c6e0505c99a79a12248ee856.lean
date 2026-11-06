import Mathlib

theorem number_theory_322552 {a b c d e : ℕ} (h₀ : 0 < a ∧ a < 10) (h₁ : 0 ≤ b ∧ b < 10)
    (h₂ : 0 ≤ c ∧ c < 10) (h₃ : 0 ≤ d ∧ d < 10) (h₄ : 0 ≤ e ∧ e < 10)
    (h₅ : (10 * a + b) ^ 3 = 10000 * a + 1000 * b + 100 * c + 10 * d + e) :
    10000 * a + 1000 * b + 100 * c + 10 * d + e = 32768 := by

  have ha1 : a > 0 := h₀.1
  have ha2 : a < 10 := h₀.2
  have hb1 : b < 10 := by linarith [h₁.2]
  have hb2 : b ≤ 9 := by linarith [h₁.2]

  have ha3 : a ≤ 9 := by linarith [ha2]

  have h8 : c < 10 := by linarith [h₂.2]
  have h9 : d < 10 := by linarith [h₃.2]
  have h10 : e < 10 := by linarith [h₄.2]

  interval_cases a <;> interval_cases b <;> omega