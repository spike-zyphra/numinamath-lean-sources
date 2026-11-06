import Mathlib

theorem algebra_20842 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a^2 + b^2 = c^2) (h1 : c = 20) (h2 : a = b) :
    (1/2) * a * b = 100 := by 
  have h3 : a^2 + b^2 = 20^2 := by
    rw [h1] at h
    linarith
  have h4 : a = b := h2
  have h5 : a^2 + a^2 = 20^2 := by
    have h6 : b = a := by linarith [h4]
    rw [h6] at h3
    nlinarith
  have h6 : a^2 = 200 := by 
    nlinarith
  have h7 : b = a := by linarith [h4]
  have h8 : (1/2) * a * b = (1/2) * a^2 := by 
    rw [show b = a by linarith [h4]]
    all_goals nlinarith
  rw [h8]
  nlinarith [h6]