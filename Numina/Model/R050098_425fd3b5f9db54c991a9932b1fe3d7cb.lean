import Mathlib

theorem algebra_5754 {a b c : ℤ} (h : ∀ x : ℝ, (x + 11) * (x + 3) * (x + 7) = x ^ 3 + a * x ^ 2 + b * x + c) :
    a + b + c = 383 := by 
  have eq1 := h 1
  have eq2 := h 0
  have eq3 := h 2
  norm_num at eq1 eq2 eq3
  
  have h2 : (a : ℝ) + (b : ℝ) + (c : ℝ) = 383 := by
    linarith 
   
  have h3 : a + b + c = 383 := by
    exact_mod_cast h2

  exact h3