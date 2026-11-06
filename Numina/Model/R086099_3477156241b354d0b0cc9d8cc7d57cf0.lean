import Mathlib

open Real
open scoped BigOperators

theorem calculus_22442 {A B C D E F : ℝ}
  (h₀ : A ∈ Set.Ioo 0 π)
  (h₁ : B ∈ Set.Ioo 0 π)
  (h₂ : C ∈ Set.Ioo 0 π)
  (h₃ : D ∈ Set.Ioo 0 π)
  (h₄ : E ∈ Set.Ioo 0 π)
  (h₅ : F ∈ Set.Ioo 0 π)
  (h₆ : A + B + C = π)
  (h₇ : D = (A + B) / 2)
  (h₈ : E = (B + C) / 2)
  (h₉ : F = (C + A) / 2)
  (h₁₀ : E - D - F = π / 2) :
  A = 2 * π / 3 := by
  rcases h₀ with ⟨hA1, hA2⟩
  rcases h₁ with ⟨hB1, hB2⟩
  rcases h₂ with ⟨hC1, hC2⟩
  rw [show D = (A + B) / 2 by linarith [h₇], show E = (B + C) / 2 by linarith [h₈], show F = (C + A) / 2 by linarith [h₉]] at h₁₀
  nlinarith [Real.pi_pos, h₆, hA1, hA2, hB1, hB2, hC1, hC2]