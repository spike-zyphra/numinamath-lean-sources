import Mathlib

theorem algebra_217052 (v : ℝ) (h : v > 0) (t : ℝ) (ht : t > 0)
    (h1 : t + 15 / 60 = v * t / (v + w)) (h2 : w > 0) :
    t = 30 / 60 := by
  have hw1 : v + w > 0 := by
    nlinarith [show 0 < w by linarith, show 0 < v by linarith]

  have eq1 : (t + 15 / 60) * (v + w) = v * t := by
    field_simp [(show v + w ≠ 0 by nlinarith [hw1])] at h1 ⊢ 
    nlinarith

  field_simp [(show v + w ≠ 0 by nlinarith [hw1])] at h1 ⊢ 
  nlinarith [sq_nonneg (w - v), sq_nonneg (t), mul_pos h h2, hw1]