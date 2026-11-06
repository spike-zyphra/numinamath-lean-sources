import Mathlib

theorem number_theory_252158 (a b c x : ℕ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < x)
    (h₁ : a * b = 13600)
    (h₂ : b = 136)
    (h₃ : c = (a - b) / 2)
    (h₄ : x^2 = a^2 + 2 * a * c + c^2) :
    c = 18 ∧ x = 118 := by
  have h5 : a * 136 = 13600 := by
    rw [h₂] at h₁ 
    exact_mod_cast h₁
  have h6 : a = 100 := by
    omega
  -- We need to prove the contradiction: 0 < c and c = 0
  have h7 : a = 100 := h6 
  have h8 : c = 0 := by
    rw [h₃]
    have h8a : a = 100 := h7 
    have h8b : b = 136 := h₂ 
    rw [h8a, h8b]
    all_goals
      omega 
  have h10 : 0 < c := by 
    omega
  omega