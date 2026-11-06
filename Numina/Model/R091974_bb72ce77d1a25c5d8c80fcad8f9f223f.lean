import Mathlib

open Real

theorem algebra_139391 {H : ℝ → ℝ} (hH : ∀ x, x ≥ 0 → H x = 1) (hH' : ∀ x, x < 0 → H x = 0) :
    ∀ x, sign x = H x - H (-x) := by
  intro x
  by_cases h1 : x > 0
  · -- Case 1: x > 0
    rw [sign_of_pos h1]
    have hHx : H x = 1 := by
      apply hH x
      linarith -- because x > 0 implies x ≥ 0
    have hH_neg_x : H (-x) = 0 := by
      apply hH' (-x)
      linarith -- because x > 0 implies -x < 0
    rw [hHx, hH_neg_x]
    all_goals norm_num
  · -- Case 2: x ≤ 0
    by_cases h2 : x = 0
    · -- Case 2: x = 0
      rw [h2]
      simp [sign_zero, hH, hH']
      all_goals norm_num
    · -- Case 3: x < 0
      have h3 : x < 0 := by
        by_contra h
        push_neg at h
        have h4 : x ≥ 0 := by linarith
        have h5 : x = 0 := by linarith [h4, h2]
        contradiction 
      rw [sign_of_neg h3]
      have hHx : H x = 0 := by
        apply hH' x
        linarith -- because x < 0
      have hH_neg_x : H (-x) = 1 := by
        apply hH (-x)
        linarith -- because -x > 0
      rw [hHx, hH_neg_x]
      all_goals norm_num