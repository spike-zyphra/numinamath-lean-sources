import Mathlib

theorem number_theory_252158 (a b c x : ℕ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < x)
    (h₁ : a * b = 13600)
    (h₂ : b = 136)
    (h₃ : c = (a - b) / 2)
    (h₄ : x^2 = a^2 + 2 * a * c + c^2) :
    c = 18 ∧ x = 118 := by
  have hb : b = 136 := h₂
  
  have ha : a = 100 := by 
    rw [hb] at h₁
    have h5 : a * 136 = 13600 := h₁
    omega
  
  have hc : c = 18 := by 
    norm_num [hb] at h₃
    omega  
  
  have h6 : x^2 = 100^2 + 2 * 100 * 18 + 18^2 := by 
    rw [ha, hc] at h₄ 
    exact h₄
  
  norm_num at h6 
  have h7 : x ≤ 181 := by nlinarith
  
  have hx : x = 118 := by 
    interval_cases x <;> omega
  
  exact ⟨hc, hx⟩
  