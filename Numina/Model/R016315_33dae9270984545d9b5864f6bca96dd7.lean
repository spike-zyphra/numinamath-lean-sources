import Mathlib

theorem number_theory_171996 (a b c d e f g h i j : ℕ)
    (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : a ≠ d) (h₃ : a ≠ e)
    (h₄ : a ≠ f) (h₅ : a ≠ g) (h₆ : a ≠ h) (h₇ : a ≠ i)
    (h₈ : a ≠ j) (h₉ : b ≠ c) (h₁₀ : b ≠ d) (h₁₁ : b ≠ e)
    (h₁₂ : b ≠ f) (h₁₃ : b ≠ g) (h₁₄ : b ≠ h) (h₁₅ : b ≠ i)
    (h₁₆ : b ≠ j) (h₁₇ : c ≠ d) (h₁₈ : c ≠ e) (h₁₉ : c ≠ f)
    (h₂₀ : c ≠ g) (h₂₁ : c ≠ h) (h₂₂ : c ≠ i) (h₂₃ : c ≠ j)
    (h₂₄ : d ≠ e) (h₂₅ : d ≠ f) (h₂₆ : d ≠ g) (h₂₇ : d ≠ h)
    (h₂₈ : d ≠ i) (h₂₉ : d ≠ j) (h₃₀ : e ≠ f) (h₃₁ : e ≠ g)
    (h₃₂ : e ≠ h) (h₃₃ : e ≠ i) (h₃₄ : e ≠ j) (h₃₅ : f ≠ g)
    (h₃₆ : f ≠ h) (h₃₇ : f ≠ i) (h₃₈ : f ≠ j) (h₃₉ : g ≠ h)
    (h₄₀ : g ≠ i) (h₄₁ : g ≠ j) (h₄₂ : h ≠ i) (h₄₃ : h ≠ j)
    (h₄₄ : i ≠ j) (h₄₅ : a = 3) (h₄₆ : b = 4) (h₄₇ : c = 1)
    (h₄₈ : d = 0) (h₄₉ : e = 8) (h₅₀ : f = 2) (h₅₁ : g = 4)
    (h₅₂ : h = 0) (h₅₃ : i = 3) (h₅₄ : j = 2) :
    396 ∣ (30000000 + 1000000 * a + 100000 * b + 10000 * c + 1000 * d + 100 * e + 10 * f + g + 10 * h + i + 10 * j) := by
  have h8 : a = i := by
    omega
  have h9 : a ≠ i := h₇
  have h10 : a = i := h8
  exfalso
  have h11 : a ≠ i := h₇
  -- The hypotheses are contradictory
  -- `a = 3` and `i = 3` implies `a = i`, which contradicts `h₇ : a ≠ i`
  have h12 : a = i := h8
  exfalso
  exact h₁ (by omega)