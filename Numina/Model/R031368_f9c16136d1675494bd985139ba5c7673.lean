import Mathlib

open Real Set
open scoped BigOperators
open Polynomial

theorem algebra_9309 {f : ℝ → ℝ} (hf : f = λ x => log ((-X^2 + 2 * X + 8).eval x)) :
  MonotoneOn f (Set.Ioc (-2) 1) := by 
  intro x hx y hy hxy 
  simp [hf] at *
  have h1 : -2 < x := hx.1 
  have h2 : x ≤ 1 := hx.2 
  have h3 : -2 < y := hy.1 
  have h4 : y ≤ 1 := hy.2 
  have h5 : -x^2 + 2 * x + 8 > 0 := by nlinarith
  have h6 : -y^2 + 2 * y + 8 > 0 := by nlinarith
  have h7 : -x^2 + 2 * x + 8 ≤ -y^2 + 2 * y + 8 := by nlinarith [hxy, mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ 1 - y by linarith)]
  have h8 : log (-x^2 + 2 * x + 8) ≤ log (-y^2 + 2 * y + 8) := Real.log_le_log (by nlinarith) (by nlinarith)
  linarith