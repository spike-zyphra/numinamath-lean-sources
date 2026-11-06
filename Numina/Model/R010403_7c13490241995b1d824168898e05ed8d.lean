import Mathlib

theorem algebra_20009 {x : ℕ} (hx : x ≠ 0) (h : (16 + 4 * x) / (12 : ℝ) = (16 + x) / (12 - x)) :
    x = 5 := by

  have h1 : (12 : ℝ) ≠ 0 := by norm_num
  have h2 : (12 - (x : ℝ)) ≠ 0 := by
    by_contra h3
    have h3' : (x : ℝ) = 12 := by linarith
    have h4 : (x : ℝ) = 12 := h3'
    have h5 : x = 12 := by exact_mod_cast h4
    rw [h5] at h
    norm_num at h <;> all_goals linarith

  field_simp [h1, h2] at h
  ring_nf at h
  
  have h3 : (x : ℝ) * (5 - (x : ℝ)) = 0 := by 
    nlinarith
  
  cases' (mul_eq_zero.mp h3) with h4 h5

  · -- Case x = 0 
    have h6 : x = 0 := by 
      exact_mod_cast h4 
    contradiction
  
  · -- Case 5 - x = 0 
    have h7 : (x : ℝ) = 5 := by 
      linarith 
    have h8 : x = 5 := by 
      exact_mod_cast h7 
    exact h8