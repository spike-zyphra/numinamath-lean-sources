import Mathlib

theorem algebra_304803 (a b c : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : 1 / a + 1 / b = 1 / (2 + 2 / 5) ∧ 1800 = a * b)
    (h₂ : 1 / b + 1 / c = 1 / (3 + 3 / 4) ∧ 1500 = b * c)
    (h₃ : 1 / c + 1 / a = 1 / (2 + 6 / 7) ∧ 1600 = c * a) :
    min (min (1800 / a) (1500 / b)) (1600 / c) = 1500 / b := by
  rcases h₀ with ⟨ha, hb, hc⟩
  rcases h₁ with ⟨h1₁, h1₂⟩
  rcases h₂ with ⟨h2₁, h2₂⟩
  rcases h₃ with ⟨h3₁, h3₂⟩
  field_simp at h1₁ h2₁ h3₁
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]