import Mathlib

theorem algebra_15873 {a : ℝ} (h : ∃ b c, ∀ x, 4*x^2 + 14*x + a = (b + c*x)^2) :
    a = 49/4 := by
  rcases h with ⟨b, c, h_eq⟩
  have eq1 := h_eq 0
  have eq2 := h_eq 1
  have eq3 := h_eq 2
  have eq4 := h_eq 3
  simp at eq1 eq2 eq3 eq4
  have h1 : a = b^2 := by 
    nlinarith
  have h2 : c^2 = 4 := by
    nlinarith [sq_nonneg (b + c), sq_nonneg (b + 2 * c), sq_nonneg (b + 3 * c)]
  have hc : c = 2 ∨ c = -2 := by 
    have h_c : c^2 = 4 := h2 
    have : c = 2 ∨ c = -2 := by
      have h1 : c^2 - 4 = 0 := by linarith
      have h2 : (c - 2) * (c + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h2) with h3 h4
      · 
        left
        linarith 
      · 
        right
        linarith 
    assumption 
  cases' hc with hc1 hc2 
  · 
    have hc1' : c = 2 := hc1 
    have h10 : b = 7 / 2 := by 
      nlinarith [sq_nonneg (b - 7 / 2)]
    nlinarith [h10, h1] 
  · 
    have hc2' : c = -2 := hc2 
    have h11 : b = -7 / 2 := by 
      nlinarith [sq_nonneg (b + 7 / 2)]
    nlinarith [h11, h1]