import Mathlib

theorem algebra_129136 {a b p q : ℝ × ℝ}
    (ha : a = 5 * p + q)
    (hb : b = p - 3 * q)
    (hp : ‖p‖ = 1)
    (hq : ‖q‖ = 2)
    (h : p.1 * q.2 - p.2 * q.1 = 1 * 2 * Real.sin (Real.pi / 3)) :
    ‖a.1 * b.2 - a.2 * b.1‖ = 16 * Real.sqrt 3 := by
  have ha1 : a.1 = 5 * p.1 + q.1 := by
    rw [ha]
    <;> simp [mul_add, mul_assoc]
  have ha2 : a.2 = 5 * p.2 + q.2 := by
    rw [ha]
    <;> simp [mul_add, mul_assoc]
  have hb1 : b.1 = p.1 - 3 * q.1 := by
    rw [hb]
    <;> simp [mul_add, mul_assoc]
    <;> ring
  have hb2 : b.2 = p.2 - 3 * q.2 := by
    rw [hb]
    <;> simp [mul_add, mul_assoc]
    <;> ring
  have cross_prod : a.1 * b.2 - a.2 * b.1 = -16 * (p.1 * q.2 - p.2 * q.1) := by
    rw [ha1, ha2, hb1, hb2]
    ring
  rw [cross_prod]
  have h1 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [Real.sin_pi_div_three]
  have hpq2 : p.1 * q.2 - p.2 * q.1 = 2 * (Real.sqrt 3 / 2) := by
    rw [h]
    rw [h1]
    <;> ring_nf
  rw [hpq2]
  simp [abs_mul, abs_of_nonneg, Real.sqrt_nonneg]
  <;> ring_nf <;> norm_num
  <;> ring
  all_goals try { norm_num }