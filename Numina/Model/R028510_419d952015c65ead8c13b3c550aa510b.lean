import Mathlib

theorem algebra_610529 (f g : ℤ → ℤ) (h₀ : ∀ x, f x + g x = 2) (h₁ : ∀ x, f (f x) = g (g x)) (h₂ : f 0 = 2022) (h₃ : ∃ k l, ∀ x, f x = k * x + l) (h₄ : ∃ k l, ∀ x, g x = k * x + l) : f 1 = 1 := by
  rcases h₃ with ⟨k, l, hf⟩
  rcases h₄ with ⟨k₂, l₂, hg⟩
  have h₅ : l = 2022 := by
    specialize hf 0
    simp at hf
    linarith [h₂, hf]
  have h₆ : l₂ = -2020 := by
    have h₇ := h₀ 0
    simp [hf, hg, h₅] at h₇
    linarith
  have h₈ : k₂ = -k := by
    have h4 := h₀ 1
    simp [hf, hg, h₅, h₆] at h4
    have h9 := h₀ 2
    simp [hf, hg, h₅, h₆] at h9
    omega
  -- Solving from h₁ now
  have h4 := h₁ 0
  simp [hf, hg, h₅, h₆, h₈] at h4
  have hk : k = -2021 := by
    omega
  -- Compute f(1)
  have h41 : f 1 = k * 1 + l := by
    specialize hf 1
    simpa using hf
  rw [h41]
  simp [h₅, hk]
  <;> omega