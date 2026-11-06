import Mathlib

theorem number_theory_94664 (a : ℕ → ℕ) (h₀ : ∃ d, ∀ n, a n = a 0 + d * n)
    (h₁ : 1 ≤ a 0 ∧ a 0 ≤ 10) (h₂ : 13 ≤ a 1 ∧ a 1 ≤ 20)
    (h₃ : 241 ≤ a 14 ∧ a 14 ≤ 250) :
    (Nat.digits 10 (a 13)).sum = 8 := by
  rcases h₀ with ⟨d, hd⟩
  have ha1 : a 1 = a 0 + d := by 
    specialize hd 1
    norm_num at hd 
    omega
  have h₁₁ := h₁.1
  have h₁₂ := h₁.2
  have h₂₁ := h₂.1
  have h₂₂ := h₂.2
  have h₃₁ := h₃.1
  have h₃₂ := h₃.2
  have ha14 : a 14 = a 0 + 14 * d := by
    specialize hd 14
    norm_num at hd 
    omega 
  have ha13 : a 13 = a 0 + 13 * d := by 
    specialize hd 13
    norm_num at hd
    omega 
  have h3 : d = 17 := by 
    omega 
  have ha0 : a 0 = 3 := by 
    omega 
  have ha13_val : a 13 = 224 := by 
    rw [ha13]
    omega 
  rw [ha13_val]
  norm_num