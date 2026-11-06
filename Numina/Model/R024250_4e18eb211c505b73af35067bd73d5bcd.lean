import Mathlib

theorem algebra_274342 {a b c S : ℕ} (ha : a + b = 1014) (hc : c - b = 497) (h : a > b)
    (hS : S = a + b + c) : S ≤ 2017 := by
  have h1 : b ≤ 1014 := by 
    omega
  have hc' : c = b + 497 := by
    omega
  have hS' : S = 1511 + b := by
    rw [hS]
    omega
  have h2 : b ≤ 506 := by
    have h3 : a > b := h
    omega
  omega