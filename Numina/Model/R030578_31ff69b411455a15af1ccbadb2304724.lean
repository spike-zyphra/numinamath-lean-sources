import Mathlib

theorem number_theory_114612 (x : ℤ) :
    ∃ q : ℚ, x^3 - 6 * x^2 + 12 * x + 29 = q^3 ↔ x = -2 ∨ x = 5 := by 
  by_cases h : x = -2 ∨ x = 5
  · -- Assume x = -2 or x = 5.
    rcases h with (h | h)
    · -- Case x = -2.
      use (-3 : ℚ)
      have hx : x = -2 := by tauto
      rw [show (x : ℚ) = (-2 : ℚ) by exact_mod_cast hx]
      norm_num
      all_goals tauto
    · -- Case x = 5.
      use (4 : ℚ)
      have hx : x = 5 := by tauto
      rw [show (x : ℚ) = (5 : ℚ) by exact_mod_cast hx]
      norm_num
      all_goals tauto
  · -- When x is neither -2 nor 5.
    use (0 : ℚ)
    constructor
    · -- Assume $(x^3 - 6 x^2 + 12 x + 29 : ℚ) = 0^3$.
      intro h_eq
      have h3 : (x ^ 3 - 6 * x^2 + 12 * x + 29 : ℚ) = (0 : ℚ) := by
        have h0 : (x ^ 3 - 6 * x^2 + 12 * x + 29 : ℚ) = (0 : ℚ)^3 := by
          simpa using h_eq
        norm_num at h0 ⊢
        linarith
      have h4 : x ^ 3 - 6 * x ^ 2 + 12 * x + 29 = (0 : ℤ) := by
        exact_mod_cast h3
      have h5 : (x - 2)^3 = -37 := by
        nlinarith
      -- From (x - 2)^3 = -37, show contradiction as no integer solution
      have h7 : x ≤ 5 := by
        nlinarith [sq_nonneg ((x - 2) : ℤ), sq_nonneg ((x - 2 + 3 : ℤ)), sq_nonneg ((x - 2 - 3 : ℤ))]
      have h8 : x ≥ -4 := by
        nlinarith [sq_nonneg ((x - 2) : ℤ), sq_nonneg ((x - 2 + 3 : ℤ)), sq_nonneg ((x - 2 - 3 : ℤ))]
      interval_cases x <;> omega
    · -- Assume x = -2 ∨ x = 5.
      intro h_eq
      tauto