import Mathlib

theorem algebra_128219 (p : ℤ) :
    ∃ a b : ℚ, ∃ x : ℝ, x^5 - p * x - 1 = 0 ∧ x^2 - a * x + b = 0 ↔ p = 0 ∨ p = 2 := by
  by_cases h : p = 0 ∨ p = 2
  · rcases h with (h | h)
    · -- Case p = 0
      use (0 : ℚ)
      use (-1 : ℚ)
      use 1
      simp [h]
      <;> norm_num
    · -- Case p = 2
      use (0 : ℚ)
      use (-1 : ℚ)
      use (-1 : ℝ)
      simp [h]
      <;> norm_num
  · -- Case p ≠ 0 and p ≠ 2
    push_neg at h
    use (0 : ℚ)
    use (1 : ℚ)
    use 1
    simp [h]
    <;> norm_num
    <;> tauto