import Mathlib

open Finset

theorem algebra_142638 {a b c n : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : 0 < n) :
    (a ^ b) ^ n = a ^ (b * n) := by 
  rw [pow_mul]