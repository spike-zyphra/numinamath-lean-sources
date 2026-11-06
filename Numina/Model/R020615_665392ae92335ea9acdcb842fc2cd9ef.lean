import Mathlib

theorem algebra_133102 {a b p q : ℝ × ℝ}
    (ha : a = p + 4 * q) (hb : b = 2 * p - q)
    (hp : ‖p‖ = 7) (hq : ‖q‖ = 2)
    (h : p.1 * q.2 - p.2 * q.1 = 7 * 2 * Real.sin (Real.pi / 3)) :
    ‖a.1 * b.2 - a.2 * b.1‖ = 63 * Real.sqrt 3 := by 
  have h1 : a.1 * b.2 - a.2 * b.1 = 9 * (q.1 * p.2 - p.1 * q.2) := by
    rw [ha, hb]
    simp [mul_add, add_mul, mul_sub, sub_mul]
    ring
  have h2 : a.1 * b.2 - a.2 * b.1 = -9 * (p.1 * q.2 - p.2 * q.1) := by
    rw [h1]
    ring_nf
  have h4 : a.1 * b.2 - a.2 * b.1 = -126 * Real.sin (Real.pi / 3) := by 
    rw [h2]
    rw [show p.1 * q.2 - p.2 * q.1 = 7 * 2 * Real.sin (Real.pi / 3) by linarith [h] ]
    ring
  have h5 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have h6 : a.1 * b.2 - a.2 * b.1 = -63 * Real.sqrt 3 := by
    rw [h4, h5]
    ring
  have h7 : ‖a.1 * b.2 - a.2 * b.1‖ = ‖(-63 * Real.sqrt 3 : ℝ)‖ := by 
    rw [show a.1 * b.2 - a.2 * b.1 = (-63 * Real.sqrt 3 : ℝ) by linarith [h6] ]
  have h8 : Real.sqrt 3 > 0 := by
    apply Real.sqrt_pos.mpr
    all_goals linarith
  have h9 : ‖(-63 * Real.sqrt 3 : ℝ)‖ = 63 * Real.sqrt 3 := by 
    have h10 : (-63 * Real.sqrt 3 : ℝ) < 0 := by 
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith) ]
    simp [abs_of_neg h10]
    all_goals nlinarith
  rw [h7, h9]
  all_goals linarith