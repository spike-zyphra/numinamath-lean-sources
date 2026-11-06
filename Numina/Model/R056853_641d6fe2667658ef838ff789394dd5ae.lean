import Mathlib

theorem algebra_304223 {a b c S : ℕ} (ha : a + b = 1014) (hc : c - b = 497)
    (h : a > b) (hS : S = a + b + c) :
    S ≤ 2017 := by 
  omega