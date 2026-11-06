import Mathlib

theorem algebra_148964 {p q : ℝ × ℝ} (hp : ‖p‖ = 5) (hq : ‖q‖ = 4)
    (h : p.1 * q.2 - p.2 * q.1 = 5 * 4 * Real.sin (Real.pi / 4)) :
    (4 * p.1 - q.1) * (p.2 + 2 * q.2) - (4 * p.2 - q.2) * (p.1 + 2 * q.1) = 90 * Real.sqrt 2 := by
  have h1 : (4 * p.1 - q.1) * (p.2 + 2 * q.2) - (4 * p.2 - q.2) * (p.1 + 2 * q.1) =
    9 * (p.1 * q.2 - p.2 * q.1) := by
    simp [mul_add, mul_sub, sub_mul]
    ring
  rw [h1]
  rw [h]
  have h2 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  rw [h2]
  ring_nf