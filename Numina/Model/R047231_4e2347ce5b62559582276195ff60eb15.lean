import Mathlib

open Real
open scoped BigOperators

theorem algebra_142274 {a b p q : ℝ × ℝ}
  (ha : a = p + 3 * q)
  (hb : b = p - 2 * q)
  (hp : ‖p‖ = 2)
  (hq : ‖q‖ = 3)
  (h : p.1 * q.2 - p.2 * q.1 = 2 * 3 * sin (π / 3)) :
  ‖a.1 * b.2 - a.2 * b.1‖ = 15 * sqrt 3 := by
  have h1 : a.1 = p.1 + 3 * q.1 := by
    rw [ha]
    all_goals simp
  have h2 : a.2 = p.2 + 3 * q.2 := by
    rw [ha]
    all_goals simp
  have h3 : b.1 = p.1 - 2 * q.1 := by
    rw [hb]
    all_goals simp
  have h4 : b.2 = p.2 - 2 * q.2 := by
    rw [hb]
    all_goals simp
  have h5 : a.1 * b.2 - a.2 * b.1 = -5 * (p.1 * q.2 - p.2 * q.1) := by
    rw [h1, h2, h3, h4]
    ring
  have h6 : p.1 * q.2 - p.2 * q.1 = 3 * sqrt 3 := by
    have h7 : sin (π / 3) = Real.sqrt 3 / 2 := by
      rw [sin_pi_div_three]
    rw [h7] at h
    linarith
  have h8 : a.1 * b.2 - a.2 * b.1 = -15 * sqrt 3 := by
    rw [h5, h6]
    all_goals ring
  rw [show ‖a.1 * b.2 - a.2 * b.1‖ = ‖(-15 * sqrt 3 : ℝ)‖ by
    rw [show a.1 * b.2 - a.2 * b.1 = -15 * sqrt 3 by linarith [h8]]
  ]
  have h9 : ‖(-15 * sqrt 3 : ℝ)‖ = 15 * sqrt 3 := by
    have h10 : sqrt 3 ≥ 0 := by apply Real.sqrt_nonneg
    simp [abs_mul, abs_of_nonneg, abs_of_nonneg]
    <;> ring_nf <;> norm_num
  rw [h9]