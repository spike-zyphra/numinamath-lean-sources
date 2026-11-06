import Mathlib

theorem algebra_198876 (a b c d e f : ℝ)
    (h₀ : c = a + b)
    (h₁ : d = b + c)
    (h₂ : e = c + d)
    (h₃ : f = d + e)
    (h₄ : e = 10) :
    a + b + c + d + e + f = 40 := by
  have h5 : c + d = 10 := by linarith [h₂, h₄]
  have h6 : d = a + 2 * b := by 
    rw [show c = a + b by linarith [h₀]] at h₁ 
    linarith [h₁]
  have h7 : 2 * a + 3 * b = 10 := by 
    have h8 : c = a + b := h₀ 
    have h9 : d = a + 2 * b := h6 
    have h10 : c + d = 10 := h5 
    rw [show c = a + b by linarith, show d = a + 2 * b by linarith] at h10 
    linarith 
  -- Now compute the total sum.
  -- Total sum: a + b + c + d + e + f
  -- Substituting variables:
  -- a: a
  -- b: b
  -- c: a + b
  -- d: a + 2b
  -- e: 10
  -- f: (a + 2b) + 10
  have h8 : a + b + c + d + e + f = 40 := by 
    have h9 : c = a + b := h₀ 
    have h10 : d = a + 2 * b := h6 
    have h11 : e = 10 := h₄ 
    have h12 : f = d + e := h₃ 
    rw [show c = a + b by linarith, show d = a + 2 * b by linarith, show e = 10 by linarith, show f = d + e by linarith] 
    have h14 : 2 * a + 3 * b = 10 := h7 
    linarith 
  linarith [h8]