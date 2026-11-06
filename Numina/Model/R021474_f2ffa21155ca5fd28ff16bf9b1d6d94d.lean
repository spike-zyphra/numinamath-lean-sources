import Mathlib

theorem algebra_105218 (k : ℤ) :
    ∃ x : ℚ, x ^ 2017 - x ^ 2016 + x ^ 2 + k * x + 1 = 0 ↔ k = -2 ∨ k = 0 := by 
  by_cases h : k = -2
  · -- If k = -2, we pick x = 1
    use (1 : ℚ)
    norm_num [h]
    <;> omega
  · -- If k ≠ -2 
    by_cases h2 : k = 0
    · -- If k = 0, we pick x = -1
      use (-1 : ℚ)
      norm_num [h2]
      <;> omega
    · -- Assume k different from -2 and 0, pick x = 0
      use (0 : ℚ)
      have h3 : k ≠ -2 := h
      have h4 : k ≠ 0 := h2
      constructor
      · -- Forward direction
        intro h5
        norm_num at h5
      · -- Backward direction
        intro h5
        exfalso
        have h51 : k = -2 ∨ k = 0 := by 
          tauto
        cases h51 with
        | inl h52 =>
          tauto
        | inr h53 =>
          tauto