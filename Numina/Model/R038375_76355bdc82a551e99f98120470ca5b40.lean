import Mathlib

theorem algebra_296583 (a b c x : ℝ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    ((x + b) * (x + c)) / ((a - b) * (a - c)) +
    ((x + c) * (x + a)) / ((b - c) * (b - a)) +
    ((x + a) * (x + b)) / ((c - a) * (c - b)) = 1 := by
  have h1 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith 
  have h2 : a - c ≠ 0 := by
    intro h 
    apply hc 
    linarith 
  have h3 : b - c ≠ 0 := by 
    intro h 
    apply hb 
    linarith 
  have h4 : b - a ≠ 0 := by 
    intro h 
    have : a = b := by linarith 
    tauto 
  have h5 : c - a ≠ 0 := by 
    intro h 
    have : a = c := by linarith 
    tauto 
  have h6 : c - b ≠ 0 := by 
    intro h 
    have : b = c := by linarith 
    tauto 
  field_simp [(show a - b ≠ 0 by intro h; apply ha; linarith), 
          (show a - c ≠ 0 by intro h; apply hc; linarith), 
          (show b - c ≠ 0 by intro h; apply hb; linarith), 
          (show b - a ≠ 0 by intro h; apply ha; linarith), 
          (show c - a ≠ 0 by intro h; apply hc; linarith), 
          (show c - b ≠ 0 by intro h; apply hb; linarith)]
  ring