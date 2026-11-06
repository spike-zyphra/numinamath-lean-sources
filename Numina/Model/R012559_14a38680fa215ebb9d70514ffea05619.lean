import Mathlib


theorem algebra_292801 (c m a n : ℝ) :
    ∃ x, c * x ^ 2 + m * x - a = 0 ∨ a * x ^ 2 + n * x + c = 0 := by
  by_cases h : c = 0
  · -- If c = 0, then the second equation becomes a x^2 + n x = 0, which has root x = 0.
    use 0
    right
    rw [h]
    ring
  · -- Assume c ≠ 0
    by_cases ha : a = 0
    · -- If a = 0, then the first equation becomes c x^2 + m x = 0, which has root x = 0.
      use 0
      left
      rw [ha]
      ring
    · -- Assume a ≠ 0 and c ≠ 0
      have h1 : m ^ 2 + 4 * c * a ≥ 0 ∨ n ^ 2 - 4 * a * c ≥ 0 := by
        by_contra h2
        push_neg at h2
        have h2 : m ^ 2 + 4 * c * a < 0 := by linarith
        have h3 : n ^ 2 - 4 * a * c < 0 := by linarith
        have h4 : m ^ 2 + n ^ 2 < (0 : ℝ) := by nlinarith
        have h5 : m ^ 2 ≥ 0 := sq_nonneg m
        have h6 : n ^ 2 ≥ 0 := sq_nonneg n
        have h7 : m ^ 2 + n ^ 2 ≥ 0 := by linarith
        linarith
      cases h1 with
      | inl h1 =>
        have h3 : ∃ x, c * x ^ 2 + m * x - a = 0 := by
          use (-m + Real.sqrt (m ^ 2 + 4 * c * a)) / (2 * c)
          have h4 : Real.sqrt (m ^ 2 + 4 * c * a) ^ 2 = m ^ 2 + 4 * c * a := by
            rw [Real.sq_sqrt]
            linarith
          field_simp [show c ≠ 0 by exact h]
          nlinarith [Real.sqrt_nonneg (m ^ 2 + 4 * c * a), h4]
        rcases h3 with ⟨x, hx⟩
        use x
        left
        exact hx
      | inr h1 =>
        have h3 : ∃ x, a * x ^ 2 + n * x + c = 0 := by
          use (-n + Real.sqrt (n ^ 2 - 4 * a * c)) / (2 * a)
          have h4 : Real.sqrt (n ^ 2 - 4 * a * c) ^ 2 = n ^ 2 - 4 * a * c := by
            rw [Real.sq_sqrt]
            linarith
          field_simp [show a ≠ 0 by
            intro h0
            apply ha
            linarith
          ]
          nlinarith [Real.sqrt_nonneg (n ^ 2 - 4 * a * c), h4]
        rcases h3 with ⟨x, hx⟩
        use x
        right
        exact hx