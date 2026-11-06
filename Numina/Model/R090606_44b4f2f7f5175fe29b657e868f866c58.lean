import Mathlib

theorem algebra_7292 {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a > b ∧ b > c) (h2 : a^2 + (a - b)^2 + (a - c)^2 = 50) :
    c = 1 := by 
  have h3 : a > b := h1.1
  have h4 : b > c := h1.2
  have h5 : a ≤ 7 := by
    by_contra h
    push_neg at h
    have h6 : a >= 8 := by linarith
    have h7 : a^2 >= 64 := by nlinarith
    have h8 : a^2 + (a - b)^2 + (a - c)^2 > 50 := by 
      nlinarith [h6, show b < a by linarith, show c < b by linarith]
    linarith
  -- Since a is at most 7
  have h6 : b <= 6 := by 
    omega
  have h7 : c <= 5 := by 
    omega
  interval_cases a <;> interval_cases b <;> interval_cases c
  <;> omega