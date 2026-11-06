import Mathlib

open Real
open scoped BigOperators

theorem inequalities_292718 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
  (hc : 0 < c) (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  (a + b) / (a + b + c) > 1 / 2 := by
  have h1 : 0 < a + b + c := by linarith
  apply (lt_div_iff₀ h1).mpr
  linarith