import Mathlib

theorem algebra_325328 {a b : ℝ} (ha : a ≠ b) (h : (a - b) * b = a * (b - a)) :
    (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0) := by 
  have h1 : (a - b) * b = a * (b - a) := h
  -- Expanding both sides of given condition
  -- Left side: $a \cdot b - b^2$
  -- Right side: $a \cdot b - a^2$
  -- Therefore $a \cdot b - b^2 = a \cdot b - a^2$ which simplifies to $a^2 = b^2$
  have h2 : a^2 - b^2 = 0 := by
    linarith
  
  have h3 : (a - b) * (a + b) = 0 := by 
    ring_nf at h2 ⊢ 
    linarith

  cases (mul_eq_zero.1 h3) with
  | inl h4 => 
    exfalso 
    apply ha 
    linarith
  
  | inr h5 => 
    have h6 : a = -b := by linarith
    by_cases h7 : b > 0 
    · 
      have h8 : a < 0 := by linarith [h6, h7]
      left 
      exact ⟨h8, h7⟩
    
    · 
      have h7' : b ≤ 0 := by nlinarith 
      have h8 : b < 0 := by
        by_contra h9 
        push_neg at h9 
        have h9' : b = 0 := by linarith 
        have h10 : a = 0 := by linarith [h6, h9']
        have h11 : a = b := by linarith [h10, h9']
        contradiction 
      have h9 : a > 0 := by linarith [h6, h8]
      right 
      exact ⟨h9, h8⟩