import Mathlib

theorem algebra_187631 {a b c : ℤ} (h : ∀ x, (x - a) * (x - 6) + 1 = (x + b) * (x + c)) :
    a = 4 ∨ a = 8 := by

  have h1 := h 0 
  have h2 := h 1 
  have h3 := h 6
  have h4 := h a

  have h5 : (6 + b) * (6 + c) = 1 := by 
    nlinarith 

  have h6 : (6 + b) = 1 ∨ (6 + b) = -1 := by 
    apply Int.eq_one_or_neg_one_of_mul_eq_one 
    exact h5 
  cases h6 with 
  | inl h7 =>
    have hb1 : b = -5 := by linarith
    have hc1 : c = -5 := by
      have h5 : (6 + b) * (6 + c) = 1 := by
        nlinarith 
      rw [show 6 + b = 1 by linarith] at h5
      have hc : 6 + c = 1 := by
        linarith 
      linarith 

    have h7 : a = 4 := by 
      rw [hb1, hc1] at h1 
      linarith 
    left 
    linarith

  | inr h8 =>
    -- if 6 + b = -1, then b = -7
    have hb2 : b = -7 := by linarith 
    -- From h5: (6+b)(6+c) =1 =>6+c=-1 =>c=-7
    have hc2 : c = -7 := by 
      have h5 : (6 + b) * (6 + c) = 1 := by
        nlinarith 
      rw [show 6 + b = -1 by linarith] at h5 
      have hc : 6 + c = -1 := by 
        linarith 
      linarith 

    -- From h1: 6a+1 = (-7)(-7)=49 =>6a=48 =>a=8
    have h81 : a = 8 := by 
      rw [hb2, hc2] at h1 
      linarith 
    right 
    linarith