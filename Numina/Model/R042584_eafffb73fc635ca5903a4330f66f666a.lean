import Mathlib

theorem algebra_231521 {a b c : ℤ} (h : ∀ x, (x - a) * (x - 10) + 1 = (x + b) * (x + c)) :
    a = 8 ∨ a = 12 := by 
  have eq1 := h 10 
  norm_num at eq1
  have eq2 := h 0
  norm_num at eq2 
  have h1 : (10 + b) * (10 + c) = 1 := by 
    nlinarith 
  have h2 : (10 + b) = 1 ∨ (10 + b) = -1 := by 
    apply Int.eq_one_or_neg_one_of_mul_eq_one 
    exact h1 
  rcases h2 with (h3 | h3)
  · -- Case 1: 10 + b = 1, so b = -9 
    have hb1 : b = -9 := by linarith 
    -- Then 10 + c = 1, so c = -9 
    have hc1 : c = -9 := by 
      rw [hb1] at h1 
      nlinarith 
    -- Now, a = 8 
    have eq_a1 : a = 8 := by 
      rw [hb1, hc1] at eq2 
      nlinarith 
    -- So the disjunction is satisfied with a = 8 
    left 
    exact eq_a1 
  · -- Case 2: 10 + b = -1, so b = -11 
    have hb2 : b = -11 := by linarith 
    -- Then 10 + c = -1, so c = -11 
    have hc2 : c = -11 := by 
      rw [hb2] at h1 
      nlinarith 
    -- Now, a = 12 
    have eq_a2 : a = 12 := by 
      rw [hb2, hc2] at eq2 
      nlinarith 
    -- So the disjunction is satisfied with a = 12 
    right 
    exact eq_a2