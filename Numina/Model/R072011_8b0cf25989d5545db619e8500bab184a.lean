import Mathlib

theorem algebra_157828 {p q : ℝ × ℝ} (hp : ‖p‖ = 3) (hq : ‖q‖ = 4)
    (h : p.1 * q.2 - p.2 * q.1 = 3 * 4 * Real.sin (Real.pi / 4)) :
    (6 * p - q).1 * (p + q).2 - (6 * p - q).2 * (p + q).1 = 42 * Real.sqrt 2 := by
  have h1 : (6 * p - q).1 * (p + q).2 - (6 * p - q).2 * (p + q).1 = 7 * (p.1 * q.2 - p.2 * q.1) := by
    simp [mul_add, mul_sub, sub_mul]
    ring
  rw [h1, h]
  have h2 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
    rw [Real.sin_pi_div_four]
    <;> ring_nf
    <;> field_simp
    <;> ring
  rw [h2]
  ring_nf
  <;> field_simp
  <;> ring_nf
  <;> nlinarith
  all_goals
    tauto
  <;> try linarith [Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]