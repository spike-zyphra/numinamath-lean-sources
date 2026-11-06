import Mathlib

open Real
open scoped BigOperators

theorem algebra_153936 {a b p q : ℝ × ℝ}
  (ha : a = 3 * p - q)
  (hb : b = p + 2 * q)
  (hp : ‖p‖ = 3)
  (hq : ‖q‖ = 4)
  (h : p.1 * q.2 - p.2 * q.1 = 3 * 4 * sin (π / 3)) :
  ‖a.1 * b.2 - a.2 * b.1‖ = 42 * sqrt 3 := by
  have h1 : sin (π / 3) = Real.sqrt 3 / 2 := by
    rw [sin_pi_div_three]
  rw [h1] at h
  have h2 : p.1 * q.2 - p.2 * q.1 = 6 * Real.sqrt 3 := by
    linarith
  have h3 : a.1 * b.2 - a.2 * b.1 = 7 * (p.1 * q.2 - p.2 * q.1) := by
    rw [ha, hb]
    simp [mul_add, mul_sub]
    <;> ring_nf <;> simp [mul_add, mul_sub]
    <;> ring_nf <;> linarith
  rw [h2] at h3
  have h4 : a.1 * b.2 - a.2 * b.1 = 42 * Real.sqrt 3 := by
    linarith
  rw [h4]
  simp
  <;> ring_nf <;> norm_num