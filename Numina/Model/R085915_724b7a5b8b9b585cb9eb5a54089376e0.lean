import Mathlib

open Real
open scoped BigOperators

theorem inequalities_211059 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
  (h : a + b + c + d = 360) :
  a + b > c - d ∨ a + c > b - d ∨ a + d > b - c ∨ b + c > a - d ∨ b + d > a - c ∨ c + d > a - b := by 
  by_contra h1
  push_neg at h1
  linarith