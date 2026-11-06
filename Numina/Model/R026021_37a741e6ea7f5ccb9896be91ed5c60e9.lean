import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_203650 (a b c d : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
  (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1) :
  (a + b + c + d + 1)^2 ≥ 4 * (a^2 + b^2 + c^2 + d^2) := by
  have h1 : a ≥ 0 := by linarith
  have h2 : b ≥ 0 := by linarith
  have h3 : c ≥ 0 := by linarith
  have h4 : d ≥ 0 := by linarith
  have ha2 : a ≤ 1 := by linarith
  have hb2 : b ≤ 1 := by linarith
  have hc2 : c ≤ 1 := by linarith
  have hd2 : d ≤ 1 := by linarith
  have h1' : a^2 ≤ a := by
    nlinarith
  have hb2' : b^2 ≤ b := by
    nlinarith
  have hc2' : c^2 ≤ c := by
    nlinarith
  have hd2' : d^2 ≤ d := by
    nlinarith
  nlinarith [sq_nonneg (a + b + c + d - 1), sq_nonneg (a - 1/2), sq_nonneg (b - 1/2), sq_nonneg (c - 1/2), sq_nonneg (d - 1/2), mul_nonneg (show a ≥ 0 by linarith) (show (1 - a) ≥ 0 by linarith), mul_nonneg (show b ≥ 0 by linarith) (show (1 - b) ≥ 0 by linarith), mul_nonneg (show c ≥ 0 by linarith) (show (1 - c) ≥ 0 by linarith), mul_nonneg (show d ≥ 0 by linarith) (show (1 - d) ≥ 0 by linarith)]