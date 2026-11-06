import Mathlib

theorem calculus_22452 (a b : ℝ × ℝ) (hb : b = (1, -3)) (h : a.1 * b.1 + a.2 * b.2 = 2) :
    let c := (a.1 * b.1 + a.2 * b.2) / (b.1 ^ 2 + b.2 ^ 2)
    (c * b.1, c * b.2) = (1 / 5, -3 / 5) := by 
  rw [hb] at h ⊢ 
  have h1 : a.1 * (1 : ℝ) + a.2 * (-3 : ℝ) = 2 := by
    simpa using h
  have h2 : (1 : ℝ) ^ 2 + (-3 : ℝ) ^ 2 = 10 := by
    norm_num
  have hc : (a.1 * (1 : ℝ) + a.2 * (-3 : ℝ)) / ((1 : ℝ) ^ 2 + (-3 : ℝ) ^ 2) = (1 / 5 : ℝ) := by
    rw [show (a.1 * (1 : ℝ) + a.2 * (-3 : ℝ)) = 2 by linarith [h1]]
    rw [h2]
    all_goals norm_num
  simp_all [hc]
  all_goals norm_num