import Mathlib

theorem algebra_19959 {x : ℝ} (hx : x^2 + 4 * x - 21 ≠ 0) :
    x < -7 ∨ x ∈ Set.Ioo (-7) 3 ∨ x > 3 := by
  by_cases h1 : x < -7
  · -- Case 1: x < -7
    left
    exact h1
  · -- Case 2: x ≥ -7
    by_cases h2 : x < 3
    · -- Subcase 2a: -7 ≤ x < 3
      have h3 : -7 < x := by
        by_contra h
        push_neg at h
        have : x = -7 := by linarith
        have h0 : x^2 + 4 * x - 21 = 0 := by
          rw [this]
          norm_num
        contradiction
      have h4 : x < 3 := h2
      right
      left
      exact ⟨h3, h4⟩
    · -- Subcase 2b: x ≥ 3
      have h4 : x > 3 := by
        by_contra h
        push_neg at h
        have : x = 3 := by linarith
        have h0 : x^2 + 4 * x - 21 = 0 := by
          rw [this]
          norm_num
        contradiction
      right
      right
      linarith