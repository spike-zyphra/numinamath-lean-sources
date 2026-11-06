import Mathlib

theorem algebra_9334 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hfpos : ∀ x > 0, f x = x ^ 2 - 2 * x + 3) :
    ∀ x, f x = if x < 0 then -x ^ 2 - 2 * x - 3 else (if x = 0 then 0 else x ^ 2 - 2 * x + 3) := by
  intro x
  by_cases h1 : x < 0
  · -- Case 1: x < 0
    have h2 : -x > 0 := by linarith
    have h3 : f (-x) = (-x) ^ 2 - 2 * (-x) + 3 := hfpos (-x) h2
    have h4 : f (-x) = -f x := hodd x
    have h5 : f x = -x ^ 2 - 2 * x - 3 := by
      rw [h4] at h3
      linarith
    simp [h1, h5]
  · -- Case 2: ¬x < 0, so x ≥ 0
    by_cases h2 : x = 0
    · -- Case 2a: x = 0
      have h3 : f x = 0 := by
        have h4 : f (-x) = -f x := hodd x
        simp [show x = (0 : ℝ) by linarith] at h4 ⊢
        all_goals linarith
      rw [h2] at h3
      simp [h2, h3]
    · -- Case 2b: x > 0
      have h5 : x > 0 := by
        by_contra h
        push_neg at h
        have h6 : x = 0 := by 
          linarith
        contradiction
      have h7 : f x = x ^ 2 - 2 * x + 3 := hfpos x h5
      simp [h1, h2, h7]