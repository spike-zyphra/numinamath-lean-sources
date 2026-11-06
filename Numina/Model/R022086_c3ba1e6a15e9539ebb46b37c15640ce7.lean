import Mathlib

theorem number_theory_236944 (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 7) (h1 : 3600 = 2 ^ a * 3 ^ b * 4 ^ c * 5 ^ d) :
    c = 1 := by
  have h2 : a + b + c + d = 7 := h
  have h4 : a ≤ 4 := by 
    have h5 : b ≥ 1 := by linarith
    have h6 : c ≥ 1 := by linarith
    have h7 : d ≥ 1 := by linarith
    omega
  have h5 : b ≤ 5 := by 
    have h6 : a ≥ 1 := by linarith
    have h7 : c ≥ 1 := by linarith
    have h8 : d ≥ 1 := by linarith
    omega
  have h6 : c ≤ 5 := by 
    have h7 : a ≥ 1 := by linarith
    have h8 : b ≥ 1 := by linarith
    have h9 : d ≥ 1 := by linarith
    omega
  have h7 : d ≤ 5 := by 
    have h8 : a ≥ 1 := by linarith
    have h9 : b ≥ 1 := by linarith
    have h10 : c ≥ 1 := by linarith
    omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega