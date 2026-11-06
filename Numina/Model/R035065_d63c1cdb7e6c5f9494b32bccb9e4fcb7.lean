import Mathlib

open Real

theorem inequalities_604960 (a b c d x y z t : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) (ht : 1 ≤ t)
    (h : a + b + c + d + x + y + z + t = 8) :
    a^2 + b^2 + c^2 + d^2 + x^2 + y^2 + z^2 + t^2 ≤ 28 := by
  have h1 : a ^ 2 ≤ a := by
    have h1 : 0 ≤ a := by linarith 
    have h2 : a ≤ 1 := by linarith
    nlinarith
  have h2 : b ^ 2 ≤ b := by
    have h1 : 0 ≤ b := by linarith 
    have h2 : b ≤ 1 := by linarith
    nlinarith
  have h3 : c ^ 2 ≤ c := by
    have h1 : 0 ≤ c := by linarith 
    have h2 : c ≤ 1 := by linarith
    nlinarith
  have h4 : d ^ 2 ≤ d := by
    have h1 : 0 ≤ d := by linarith 
    have h2 : d ≤ 1 := by linarith
    nlinarith
  have h14 : x^2 + y^2 + z^2 + t^2 ≥ 2 * x + 2 * y + 2 * z + 2 * t - 4 := by
    nlinarith [sq_nonneg (x-1), sq_nonneg (y-1), sq_nonneg (z-1), sq_nonneg (t-1)]
  nlinarith [sq_nonneg (a + b + c + d - 0), sq_nonneg ((8 - (a + b + c + d : ℝ)) - 8)]