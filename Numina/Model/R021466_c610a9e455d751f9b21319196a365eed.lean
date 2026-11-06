import Mathlib

theorem number_theory_267850 (a b c : ℕ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : b ≠ c)
    (h₃ : a * b * c = 80) (h₄ : a ∈ [1, 2, 4, 8, 16, 20]) (h₅ : b ∈ [1, 2, 4, 8, 16, 20])
    (h₆ : c ∈ [1, 2, 4, 8, 16, 20]) :
    a + b + c = 25 := by
  have ha1 : a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 8 ∨ a = 16 ∨ a = 20 := by
    simp at h₄ ⊢
    tauto
  have hb1 : b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8 ∨ b = 16 ∨ b = 20 := by
    simp at h₅ ⊢
    tauto
  have hc1 : c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 8 ∨ c = 16 ∨ c = 20 := by
    simp at h₆ ⊢
    tauto
  rcases ha1 with ha1 | ha1 | ha1 | ha1 | ha1 | ha1 <;> rcases hb1 with hb1 | hb1 | hb1 | hb1 | hb1 | hb1 <;> rcases hc1 with hc1 | hc1 | hc1 | hc1 | hc1 | hc1 <;> 
    norm_num [ha1, hb1, hc1] at h₃ ⊢ <;> 
    omega