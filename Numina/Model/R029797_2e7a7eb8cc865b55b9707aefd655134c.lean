import Mathlib

open Real

theorem number_theory_310863 {p : ℕ → ℝ}
    (hp : ∀ d, p d = logb 10 (d + 1) - logb 10 d)
    (h : p 2 = -1 / 2) :
    (p 4 + p 5 + p 6 + p 7 + p 8) / 5 = 1 / 2 := by

  have h1 : p 2 = logb 10 3 - logb 10 2 := by
    rw [hp 2]
    all_goals norm_num

  have h2 : logb 10 3 - logb 10 2 = -1 / 2 := by
    rw [h1] at h
    linarith

  have h3 : logb 10 3 > 0 := by
    apply logb_pos
    all_goals norm_num

  have h4 : logb 10 2 > 0 := by
    apply logb_pos
    all_goals norm_num

  have h5 : logb 10 3 > logb 10 2 := by
    have h6 : logb 10 3 > logb 10 2 := by
      apply Real.logb_lt_logb
      all_goals norm_num
    linarith [h6]

  linarith [h2, h3, h4, h5]