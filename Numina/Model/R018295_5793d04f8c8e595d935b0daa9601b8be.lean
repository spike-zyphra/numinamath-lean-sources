import Mathlib

theorem algebra_11749 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsum : a + Real.sqrt b + (a - Real.sqrt b) = -4) (hprod : (a + Real.sqrt b) * (a - Real.sqrt b) = 1) :
    a + b = 1 := by
  have h1 : 2 * a = -4 := by 
    linarith
  have ha2 : a = -2 := by 
    linarith
  have hb_pos : b > 0 := by
    by_contra h
    push_neg at h
    have h3 : Real.sqrt b = 0 := by
      rw [Real.sqrt_eq_zero']
      linarith
      all_goals linarith
    rw [h3] at hprod
    rw [show a = -2 by linarith] at hprod
    nlinarith [ha2]
  have h4 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith [hb_pos])
  have h2 : a^2 - b = 1 := by
    have hprod' : (a + Real.sqrt b) * (a - Real.sqrt b) = a^2 - (Real.sqrt b) ^ 2 := by
      ring
    rw [hprod'] at hprod
    nlinarith [hprod, h4]
  have hb2 : b = 3 := by 
    rw [ha2] at h2
    nlinarith
  linarith [ha2, hb2]