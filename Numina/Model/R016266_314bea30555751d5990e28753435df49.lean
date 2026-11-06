import Mathlib

theorem algebra_15160 (a b c d : ℕ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c) (h₃ : 0 < d)
    (h₄ : a < b ∧ b < c ∧ c < d) (h₅ : ∃ d, b = a + d ∧ c = b + d)
    (h₆ : ∃ r, c = b * r ∧ d = c * r) (h₇ : d - a = 30) :
    a + b + c + d = 129 := by 
  rcases h₅ with ⟨d', h₈, h₉⟩
  rcases h₆ with ⟨r, h₁₀, h₁₁⟩
  have h10 : a < b := h₄.1
  have h20 : b < c := h₄.2.1
  have h30 : c < d := h₄.2.2
  have h11 : b = a + d' := h₈
  have h12 : c = b + d' := h₉
  have h13 : c = a + 2 * d' := by 
    nlinarith [h11, h12]
  have h14 : (a + 2 * d') = (a + d') * r := by
    rw [h13] at h₁₀
    rw [h11] at h₁₀
    all_goals
      omega
  have h15 : d = c * r := h₁₁
  have h16 : d = (a + 2 * d') * r := by
    rw [h13] at h15
    all_goals 
      omega
  have h18 : d = a + 30 := by 
    omega
  have h19 : d' < 15 := by 
    nlinarith [h16, h18, h₀, h₁, h₂, h₃]
  have h20 : r ≤ 32 := by 
    nlinarith [h16, h18, h₀, h₁, h₂, h₃]
  interval_cases d' <;> try { 
    omega 
  } <;> try { 
    interval_cases r <;> omega 
  }