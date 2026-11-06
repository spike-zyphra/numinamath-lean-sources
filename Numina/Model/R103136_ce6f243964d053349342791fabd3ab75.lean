import Mathlib

open Real

theorem other_177943 {Q : ℝ} (hQ : Q > 0) (h : 10 * 10 * 10 = Q / (2 * π * 20 * 25)) :
    Q ≥ 337.5 := by
  have h1 : Q = 10 * 10 * 10 * (2 * π * 20 * 25) := by
    field_simp [show (2 * π * 20 * 25 : ℝ) ≠ 0 by positivity] at h ⊢
    nlinarith 
  rw [h1]
  have h2 : π ≥ 3.14 := by 
    linarith [Real.pi_gt_314]
  nlinarith [h2]
  all_goals linarith [Real.pi_gt_314]