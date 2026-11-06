import Mathlib

theorem algebra_300104 (a b c : ℤ) (h : ∀ x, (x - a) * (x - 10) + 1 = (x + b) * (x + c)) :
    a = 8 ∨ a = 12 := by

  have eq5 : 10 * a + 1 = b * c := by 
    specialize h 0
    nlinarith
  
  have eq6 : (10 + b) * (10 + c) = 1 := by
    specialize h 10
    nlinarith
  
  have h2 : (10 + b) * (10 + c) = 1 := eq6
  
  have h3 : (10 + b) = 1 ∨ (10 + b) = -1 := by
    apply Int.eq_one_or_neg_one_of_mul_eq_one 
    exact h2
  
  cases h3 with
  | inl h4 =>
  
    have hb1 : b = -9 := by 
      omega
  
    have hc1 : c = -9 := by
      have h5 : (10 + c) = 1 := by 
        rw [show (10 + b) = 1 by linarith [h4] ] at h2
        linarith
      omega
  
    have eq8 : a = 8 := by
      rw [hb1, hc1] at eq5
      nlinarith
  
    left
    exact eq8
  
  | inr h4 =>
  
    have hb2 : b = -11 := by
      omega
  
    have hc2 : c = -11 := by 
      have h5 : (10 + c) = -1 := by
        rw [show (10 + b) = -1 by linarith [h4] ] at h2
        linarith
      omega
  
    have eq12 : a = 12 := by 
      rw [hb2, hc2] at eq5
      nlinarith
  
    right
    exact eq12