import Mathlib

theorem algebra_137764 {a b p q : ℝ × ℝ}
    (ha : a = 2 * p - 3 * q)
    (hb : b = 3 * p + q)
    (hp : ‖p‖ = 4)
    (hq : ‖q‖ = 1)
    (h : p.1 * q.2 - p.2 * q.1 = 4 * 1 * Real.sin (Real.pi / 6)) :
    ‖a.1 * b.2 - a.2 * b.1‖ = 22 := by
  have ha1 : a.1 = 2 * p.1 - 3 * q.1 := by
    rw [ha]
    <;> simp [mul_add, mul_sub]
    <;> ring
  have ha2 : a.2 = 2 * p.2 - 3 * q.2 := by
    rw [ha]
    <;> simp [mul_add, mul_sub]
    <;> ring
  have hb1 : b.1 = 3 * p.1 + q.1 := by
    rw [hb]
    <;> simp [mul_add, mul_sub]
    <;> ring
  have hb2 : b.2 = 3 * p.2 + q.2 := by
    rw [hb]
    <;> simp [mul_add, mul_sub]
    <;> ring
  have hdet : a.1 * b.2 - a.2 * b.1 = 11 * (p.1 * q.2 - p.2 * q.1) := by
    rw [ha1, ha2, hb1, hb2]
    ring
  rw [hdet]
  rw [show p.1 * q.2 - p.2 * q.1 = 4 * 1 * Real.sin (Real.pi / 6) by linarith [h]]
  have hsin : Real.sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
  rw [hsin]
  norm_num [abs_of_nonneg]
  all_goals linarith