import Mathlib

theorem algebra_140053 (a b c d e : ℤ) (h₀ : a < b ∧ b < c ∧ c < d ∧ d < e)
    (h₁ : a + b = 21 ∧ a + c = 26 ∧ a + d = 35 ∧ a + e = 40 ∧ b + c = 49 ∧ b + d = 51 ∧ b + e = 54 ∧
      c + d = 60 ∧ c + e = 65 ∧ d + e = 79) :
    a = 6 ∧ b = 15 ∧ c = 20 ∧ d = 34 ∧ e = 45 := by
  have h2 : a + b = 21 := h₁.1
  have h3 : a + c = 26 := by linarith [h₁]
  have h4 : a + d = 35 := by linarith [h₁]
  have h5 : a + e = 40 := by linarith [h₁]
  have h6 : b + c = 49 := by linarith [h₁]
  have h7 : b + d = 51 := by linarith [h₁]
  have h8 : b + e = 54 := by linarith [h₁]
  have h9 : c + d = 60 := by linarith [h₁]
  have h10 : c + e = 65 := by linarith [h₁]
  have h11 : d + e = 79 := by linarith [h₁]
  have ha : a = 6 := by
    linarith [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  have hb : b = 15 := by
    linarith [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  have hc : c = 20 := by
    linarith [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  have hd : d = 34 := by
    linarith [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  have he : e = 45 := by
    linarith [h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  exact ⟨ha, hb, hc, hd, he⟩