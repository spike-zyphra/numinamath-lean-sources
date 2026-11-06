import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_297951 {a b c : ℝ} (ha : a > 0) (hb : b > 0)
  (hc : c = sqrt (a^2 - b^2)) (h : 2 * c = sqrt (2 * a^2)) :
  c / a = sqrt 2 / 2 := by
  have h1 : sqrt (2 * a^2) = Real.sqrt 2 * a := by
    have h2 : 2 * a ^ 2 = 2 * (a ^ 2) := by ring
    have h3 : sqrt (2 * a^2) = sqrt (2 * (a ^ 2)) := by rw [h2]
    have h4 : sqrt (2 * (a ^ 2)) = sqrt (2) * sqrt (a ^ 2) := by
      rw [Real.sqrt_mul (by positivity)]
    have h5 : sqrt (a ^ 2) = a := Real.sqrt_sq (by linarith)
    rw [h3, h4, h5]
  have h2 : 2 * c = Real.sqrt 2 * a := by
    rw [h1] at h
    linarith
  have h3 : c = Real.sqrt 2 * a / 2 := by
    nlinarith
  have h4 : c / a = Real.sqrt 2 / 2 := by
    rw [h3]
    field_simp [ha.ne.symm]
    <;> nlinarith
  exact h4