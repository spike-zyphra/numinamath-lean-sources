import Mathlib

theorem algebra_3397 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : 2 * x + 5 * y = 1) (h2 : 47 * x + 117 * y = a) :
    round a = 23 := by
  have hx_eq : x = (1 - 5 * y) / 2 := by
    linarith [h1]
  have h5 : y < 1 / 5 := by
    have hx_pos : (1 - 5 * y) / 2 > 0 := by
      have hx' : x > 0 := hx
      rw [show x = (1 - 5 * y) / 2 by linarith [hx_eq]] at hx'
      linarith
    nlinarith
  have ha_eq : a = (47 - y) / 2 := by 
    rw [show x = (1 - 5 * y) / 2 by linarith [hx_eq]] at h2 
    linarith
  rw [ha_eq]
  rw [round_eq]
  rw [Int.floor_eq_iff]
  constructor
  · -- Let's prove that $23 \leq (47 - y)/2 + 0.5$.
    have h6 : y > 0 := by linarith 
    have h9 : (47 - y) / 2 > 23.4 := by
      have h9 : y > 0 := by linarith 
      have h5 : y < 1 / 5 := by linarith [h5]
      nlinarith 
    have h14 : ((47 - y : ℝ) / 2) + (0.5 : ℝ) > (23 : ℝ) := by
      nlinarith 
    nlinarith 
  · -- Now let's prove that $(47 - y)/2 + 0.5 < 24$.
    have h6 : y > 0 := by linarith 
    have h7 : (47 - y) / 2 < 23.5 := by
      have h6 : y > 0 := by linarith 
      have h5 : y < 1 / 5 := by linarith [h5]
      nlinarith 
    have h15 : ((47 - y : ℝ) / 2) + (0.5 : ℝ) < (24 : ℝ) := by
      nlinarith 
    nlinarith