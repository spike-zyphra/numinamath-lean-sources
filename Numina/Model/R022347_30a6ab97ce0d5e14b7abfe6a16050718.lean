import Mathlib

theorem algebra_140425 (P : ℝ) (hP : P = 750000) (r : ℝ) (hr : r > 0)
    (h : P * (1 + r / 360) ^ 30 * 5 = P + 37500) :
    r = 12 := by
  rw [hP] at h
  -- Simplify the equation to get (1 + r / 360) ^ 30 = 21 / 100
  have h1 : (1 + r / 360 : ℝ) ^ 30 = 21 / 100 := by
    ring_nf at h
    nlinarith

  have h7 : (1 + r / 360 : ℝ) > 1 := by 
    have h8 : r > 0 := hr
    have h9 : r / 360 > 0 := by 
      positivity
    linarith 
  -- From h7, we know that (1 + r/360) > 1, so (1 + r/360)^30 > 1^30 = 1
  have h8 : (1 + r / 360 : ℝ) ^ 30 > (1 : ℝ) := by 
    have h9 : (1 + r / 360 : ℝ) > (1 : ℝ) := h7
    have h10 : (1 + r / 360 : ℝ) ^ 30 > (1 : ℝ) := by 
      have h11 : (1 + r / 360 : ℝ) > (1 : ℝ) := h9 
      have h12 : (1 + r / 360 : ℝ) ^ 30 > (1 : ℝ) ^ (30 : ℕ) := by 
        apply pow_lt_pow_left 
        all_goals linarith 
      have h13 : (1 : ℝ) ^ (30 : ℕ) = (1 : ℝ) := by 
        simp 
      linarith [h13] 
    linarith 
  -- Now we derive a contradiction from h1 and h8.
  nlinarith [h1, h8]