import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_253012 (f : ℝ → ℝ) (hf : f = λ x => (x + 1)^2 / (x^2 + 1)) :
    StrictMonoOn f (Icc (-1) 1) := by
  intro x hx y hy hxy
  have hx1 : -1 ≤ x := hx.1
  have hx2 : x ≤ 1 := hx.2
  have hy1 : -1 ≤ y := hy.1
  have hy2 : y ≤ 1 := hy.2
  have h1 : x < y := hxy
  have hfx : f x = (x + 1) ^ 2 / (x ^ 2 + 1) := by
    rw [hf]
  have hfy : f y = (y + 1) ^ 2 / (y ^ 2 + 1) := by
    rw [hf]
  rw [hfx, hfy]
  have h3 : (x + 1) ^ 2 / (x ^ 2 + 1) < (y + 1) ^ 2 / (y ^ 2 + 1) := by
    apply (div_lt_div_iff (by nlinarith) (by nlinarith)).mpr
    -- Show the inequality after cross-multiplication
    have h4 : x * y < 1 := by
      nlinarith [show x ≤ 1 by linarith, show -1 ≤ x by linarith, show y ≤ 1 by linarith, show -1 ≤ y by linarith, mul_nonneg (sub_nonneg.2 (show x ≥ -1 by linarith)) (sub_nonneg.2 (show y ≥ -1 by linarith)), mul_self_nonneg (x - 1), mul_self_nonneg (y - 1), sq_nonneg (x - y)]
    nlinarith [mul_self_nonneg (x - y), mul_pos (show 0 < (y - x) by linarith) (show 0 < 1 - x * y by nlinarith), mul_self_nonneg (x + 1), mul_self_nonneg (y + 1), mul_self_nonneg (x - 1), mul_self_nonneg (y - 1)]
  exact h3