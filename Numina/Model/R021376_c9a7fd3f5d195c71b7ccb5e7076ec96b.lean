import Mathlib

theorem algebra_238459 (k : ℤ) :
    ∃ x : ℤ, k * x ^ 2 - 2 * (3 * k - 1) * x + 9 * k - 1 = 0 ↔ k = -3 ∨ k = -7 := by
  by_cases h : k = -3 ∨ k = -7
  · -- Case where k = -3 ∨ k = -7
    rcases h with (r | r)
    · -- When k = -3, using x = 2
      use 2
      rw [r]
      norm_num
    · -- When k = -7, using x = 4
      use 4
      rw [r]
      norm_num
  · -- Case where k ≠ -3 ∧ k ≠ -7
    push_neg at h
    use 0
    constructor
    · -- Assume the equation holds, derive k = -3 ∨ k = -7
      intro h1
      -- Substitute x = 0 into the equation, which simplifies to 9k - 1 = 0
      -- This implies k = 1/9, which is impossible for integer k
      have h1' : 9 * k - 1 = 0 := by
        nlinarith
      have h1k : 9 * k = 1 := by
        linarith
      omega
    · -- Assume k = -3 ∨ k = -7, derive the equation holds
      intro h2
      cases h2 with
      | inl h1 =>
        -- Substitute k = -3, which contradicts h.0
        omega
      | inr h1 =>
        -- Substitute k = -7, which contradicts h.1
        omega