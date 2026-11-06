import Mathlib

open Real

theorem algebra_262836 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 1) :
    (a + b * c) / (a + b) + (b + c * a) / (b + c) + (c + a * b) / (c + a) = 2 := by

  have h1 : c = 1 - a - b := by linarith

  have eq1 : (a + b * c) / (a + b) = 1 - b := by 
    rw [h1]
    have h2 : a + b ≠ 0 := by nlinarith
    field_simp [h2]
    ring_nf
    <;> nlinarith
  
  have eq2 : (b + c * a) / (b + c) = a + b := by
    rw [h1]
    have h3 : b + (1 - a - b) ≠ 0 := by 
      have hc' : 0 < c := hc
      have h1' : c = 1 - a - b := h1
      rw [h1'] at hc'
      nlinarith
    have h4 : b + (1 - a - b) * a = (a + b) * (1 - a) := by 
      ring 
    have h5 : (b + (1 - a - b) * a) / (b + (1 - a - b)) = a + b := by 
      rw [show b + (1 - a - b) * a = (a + b) * (1 - a) by linarith [h4]]
      have h6 : (1 - a : ℝ) ≠ 0 := by 
        nlinarith
      field_simp [h6]
      <;> ring 
      all_goals nlinarith
    exact h5
  
  have eq3 : (c + a * b) / (c + a) = 1 - a := by 
    rw [h1]
    have h4 : ((1 - a - b : ℝ) + a * b) / ((1 - a - b : ℝ) + a) = 1 - a := by 
      have h5 : (1 - a - b : ℝ) + a ≠ 0 := by 
        have hc' : 0 < c := hc 
        have h1' : c = 1 - a - b := h1 
        rw [h1'] at hc' 
        nlinarith 
      have h6 : (1 - a - b + a * b : ℝ) = (1 - a) * ((1 - a - b : ℝ) + a) := by 
        ring 
      have h7 : ((1 - a - b : ℝ) + a * b) / ((1 - a - b : ℝ) + a) = (1 - a) := by 
        rw [show (1 - a - b + a * b : ℝ) = (1 - a) * ((1 - a - b : ℝ) + a) by linarith [h6]]
        have h7 : (1 - a - b + a : ℝ) ≠ 0 := by 
          have hc' : 0 < c := hc 
          have h1' : c = 1 - a - b := h1 
          rw [h1'] at hc' 
          nlinarith 
        field_simp [h7]
        <;> ring 
        all_goals nlinarith 
      linarith 
    exact h4
  
  rw [eq1, eq2, eq3]
  linarith
  all_goals linarith
  all_goals linarith