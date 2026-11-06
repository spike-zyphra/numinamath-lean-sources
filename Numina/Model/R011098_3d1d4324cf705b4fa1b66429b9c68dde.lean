import Mathlib

theorem algebra_610529 (f g : ℤ → ℤ) (h₀ : ∀ x, f x + g x = 2) (h₁ : ∀ x, f (f x) = g (g x)) (h₂ : f 0 = 2022) (h₃ : ∃ k l, ∀ x, f x = k * x + l) (h₄ : ∃ k l, ∀ x, g x = k * x + l) : f 1 = 1 := by
  rcases h₃ with ⟨k, l, hf⟩
  rcases h₄ with ⟨k', l', hg⟩
  have eq1 := h₀ 0
  simp [hf, hg] at eq1
  have eq2 := h₀ 1
  simp [hf, hg] at eq2
  have hk : k + k' = 0 := by 
    nlinarith 
  have hl : l + l' = 2 := by linarith 
  have eq3 := h₁ 0 
  simp [hf, hg] at eq3
  have hk' : k' = -k := by linarith 
  have hl' : l' = 2 - l := by linarith 
  rw [hk', hl'] at eq3 
  have heq : l = -k + 1 := by 
    nlinarith 
  have h_f0 : f 0 = l := by 
    specialize hf 0 
    simpa using hf 
  rw [h_f0] at h₂ 
  have hk2 : k = -2021 := by 
    linarith 
  have hl2 : l = 2022 := by 
    exact h₂ 
  have h1 : f 1 = k * 1 + l := hf 1 
  rw [hk2, hl2] at h1 
  linarith