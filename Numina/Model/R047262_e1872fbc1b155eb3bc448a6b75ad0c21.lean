import Mathlib

open Real

theorem calculus_23087 (x : ℝ) :
    sin x / cos x + cos x / (1 + sin x) = 1 / cos x := by
  have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  by_cases h3 : cos x = 0
  · -- cos x = 0
    have h4 : sin x ^ 2 = 1 := by 
      rw [h3] at h2
      nlinarith
    have h5 : sin x = 1 ∨ sin x = -1 := by 
      have h6 : sin x ^ 2 = 1 := h4
      rw [sq_eq_one_iff] at h6
      exact h6
    rw [h3]
    rcases h5 with (h7 | h8)
    · -- sin x = 1
      have h8 : sin x = 1 := h7
      simp [h3, h8]
      all_goals nlinarith [h2, h3, h8]
    · -- sin x = -1
      have h9 : sin x = -1 := h8
      simp [h3, h9]
      all_goals nlinarith [h2, h3, h9]
  · -- cos x ≠ 0
    have h4 : cos x ≠ 0 := by
      intro h
      apply h3
      exact h
    have h5 : 1 + sin x ≠ 0 := by
      by_contra h6
      have h7 : sin x = -1 := by linarith
      have h8 : cos x ^ 2 = 0 := by
        have h9 : cos x ^ 2 + sin x ^ 2 = 1 := by
          linarith [h2]
        rw [h7] at h9
        nlinarith
      have h11 : cos x = 0 := by
        nlinarith
      contradiction
    have eq1 : sin x / cos x + cos x / (1 + sin x) = ( sin x * (1 + sin x) + cos x ^ 2 ) / ( cos x * (1 + sin x) ) := by
      field_simp [h4, h5]
      <;> ring
    have eq2 : sin x * (1 + sin x) + cos x ^ 2 = sin x + 1 := by
      have h6 : sin x ^ 2 + cos x ^ 2 = 1 := by
        linarith [h2]
      nlinarith [h6]
    rw [eq1]
    rw [eq2]
    have h6 : sin x + 1 = (1 + sin x) := by 
      ring
    rw [h6]
    have h7 : cos x * (1 + sin x) ≠ 0 := by
      apply mul_ne_zero
      exact h4
      all_goals
      have h8 : 1 + sin x ≠ 0 := h5
      exact h8
    field_simp [h4, h5, h7]
    all_goals
      nlinarith [h2, h4, h5]