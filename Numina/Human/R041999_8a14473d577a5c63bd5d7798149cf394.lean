import Mathlib

open Real
/-Vasya chose four numbers and for each pair, he calculated the logarithm of the larger number to the base of the smaller one. This resulted in six logarithms. Four of them are 15, 20, 21, and 28. What values can the largest of all six logarithms take?-/
theorem algebra_212567 (a b c d : ℝ)  (h₆ : logb a b = 15) (h₇ : logb a c = 20) (h₉ : logb b c = 28) :
    logb b d = 28 ∨ logb c d = 420 := by
 -- prove several fundamental results
  have h1 : logb a b = log b / log a := by 
    field_simp [logb]
  have h2 : logb a c = log c / log a := by 
    field_simp [logb]
  have h3 : logb a d = log d / log a := by 
    field_simp [logb]
  have h4 : logb b c = log c / log b := by 
    field_simp [logb]
  
  rw [h1] at h₆ 
  rw [h2] at h₇ 
  rw [h4] at h₉ 

  have h10 : log a ≠ 0 := by 
    by_contra h
    rw [h] at h₆ 
    norm_num at h₆ 
  have h11 : log b ≠ 0 := by 
    by_contra h
    rw [h] at h₉ 
    norm_num at h₉ 

  have h12 : log b = 15 * log a := by
    have hne : log a ≠ 0 := h10
    field_simp [hne] at h₆ 
    linarith
  
  have h13 : log c = 20 * log a := by 
    have hne : log a ≠ 0 := h10
    field_simp [hne] at h₇ 
    linarith
  
  have h14 : log c = 28 * log b := by 
    have hne : log b ≠ 0 := h11
    field_simp [hne] at h₉ 
    linarith
  -- directly compute
  rw [h12] at h14 
  have h15 : log c = 28 * (15 * log a) := by linarith 
  have h16 : log c = 20 * log a := h13 
  have h17 : 420 * log a = 20 * log a := by 
    linarith [h15, h16]

  have h18 : (420 - 20) * log a = 0 := by 
    linarith 
  have h19 : log a = 0 := by 
    cases' (mul_eq_zero.mp h18) with h20 h21 
    · -- 420 - 20 = 0, which is false 
      norm_num at h20 
    · -- log a = 0 
      linarith 

  contradiction