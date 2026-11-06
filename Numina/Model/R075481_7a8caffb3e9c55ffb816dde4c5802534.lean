import Mathlib

theorem algebra_4148 (v : ℝ) (h : v > 0) (h1 : 210 / (v + 5) = 210 / v - 1) :
    v + 5 = 35 := by
  have eq1 : v + 5 ≠ 0 := by
    by_contra h2
    have : v = -5 := by linarith
    linarith [show v > 0 by linarith]

  have eq2 : v ≠ 0 := by
    linarith [h]

  -- Multiply through by v(v + 5) to clear denominators
  field_simp [(show v + 5 ≠ 0 by assumption), (show v ≠ 0 by assumption)] at h1
  ring_nf at h1
  
  -- Solving quadratic inequality v^2 + 5v - 1050 = 0 with the constraint v > 0
  nlinarith [sq_nonneg (v - 30), sq_nonneg (v + 35), sq_pos_of_pos (show v > 0 by linarith)]