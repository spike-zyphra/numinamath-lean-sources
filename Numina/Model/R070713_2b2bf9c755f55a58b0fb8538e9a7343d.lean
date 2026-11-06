import Mathlib

theorem inequalities_2411
    (a b : ℝ)
    (h₀ : 0 < a)
    (h₁ : b < 0)
    (h₂ : a < abs b) :
    -b > a ∧ a > -a ∧ -a > b := by 
  have h3 : abs b = -b := by 
    rw [abs_of_neg h₁]
  have h4 : a < -b := by
    rw [h3] at h₂
    linarith
  have h5 : a > -a := by
    linarith
  have h8 : -a > b := by
    linarith 
  constructor
  · linarith
  constructor
  · linarith 
  · linarith