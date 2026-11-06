import Mathlib

theorem algebra_178607 {a b c : ℝ} (h₀ : a + b + c = 0) (h₁ : a^3 + b^3 + c^3 = 0) :
    a^19 + b^19 + c^19 = 0 := by

  have h2 : a * b * c = 0 := by 
    have h2' : a^3 + b^3 + c^3 - 3 * a * b * c = (a + b + c) * (a^2 + b^2 + c^2 - (a * b + b * c + c * a)) := by 
      ring 
    rw [h₀] at h2' 
    have h3 : a^3 + b^3 + c^3 - 3 * a * b * c = 0 := by linarith 
    have h4 : a * b * c = 0 := by
      linarith [h₁, h3]
    exact h4
  
  cases' (mul_eq_zero.mp h2) with h5 h6
  cases' (mul_eq_zero.mp h5) with ha hb
  
  · -- Case where a = 0
    have ha0 : a = 0 := ha 
    have hc : c = -b := by linarith [h₀, ha0] 
    rw [ha0, hc] 
    ring_nf
  
  · -- Case where b = 0
    have hb0 : b = 0 := hb 
    have hc : c = -a := by linarith [h₀, hb0] 
    rw [hb0, hc] 
    ring_nf
  
  · -- Case where c = 0
    have hc0 : c = 0 := h6 
    have hb : b = -a := by linarith [h₀, hc0] 
    rw [hb, hc0] 
    ring_nf