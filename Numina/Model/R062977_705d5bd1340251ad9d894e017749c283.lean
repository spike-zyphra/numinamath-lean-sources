import Mathlib

theorem algebra_137852 (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
    (f : ℝ → ℝ) (h : ∀ x, f (a ^ x) = x) :
    f 1 = 0 ∧ f 2 = Real.logb a 2 := by
  have h1 : f 1 = 0 := by
    specialize h 0
    have h2 : a ^ (0 : ℝ) = 1 := by
      simp
    rw [h2] at h
    linarith

  have h2 : f 2 = Real.logb a 2 := by
    have h3 : f (a ^ (Real.logb a 2)) = Real.logb a 2 := h (Real.logb a 2)
    have h4 : a ^ (Real.logb a 2 : ℝ) = (2 : ℝ) := by
      rw [Real.rpow_logb]
      all_goals
        try linarith [ha.1, show (0 : ℝ) < 2 by norm_num, ha.2]
        try tauto
    rw [h4] at h3
    linarith
  
  constructor
  · exact h1
  · exact h2