import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11030 {r s : ℝ} (hr : r > 0) (hs : s > 0)
  (h₀ : r^2 * π = 64 * π) (h₁ : s^2 * π = 16 * π) :
  (r^2 * π / 2) + (s^2 * π / 2) = 40 * π := by 
  have hr2 : r^2 = 64 := by 
    nlinarith [Real.pi_pos]
  have hs2 : s^2 = 16 := by 
    nlinarith [Real.pi_pos]
  rw [hr2, hs2]
  linarith [Real.pi_pos]