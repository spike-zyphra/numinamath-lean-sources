import Mathlib

theorem algebra_233599 (walk run : ℝ) (h₀ : 0 < walk) (h₁ : 0 < run)
    (h₂ : walk + run = 40) (h₃ : 2 * run = 24) :
    2 * walk = 56 := by
  have h₄ : run = 12 := by
    linarith
  have h₅ : walk = 28 := by
    rw [h₄] at h₂
    linarith
  rw [h₅]
  all_goals norm_num