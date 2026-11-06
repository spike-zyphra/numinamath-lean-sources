import Mathlib

theorem number_theory_109990 (x y : ℕ) (h : x^3 - y^3 = 61) :
    x = 5 ∧ y = 4 := by
  have h1 : x^3 = y^3 + 61 := by
    omega
  have h2 : x > y := by
    by_contra h2
    push_neg at h2
    have h3 : x ≤ y := by linarith
    have h4 : x^3 ≤ y^3 := by
      have h5 : x ≤ y := h3
      have h7 : x^3 ≤ y^3 := by
        apply Nat.pow_le_pow_of_le_left
        all_goals
          omega
      omega
    omega
  have h3 : x ≤ y + 5 := by
    nlinarith [sq_nonneg (x - (y + 1) : ℤ), sq_nonneg ((x + y) : ℤ), sq_nonneg (x - y : ℤ)
          , h1, sq_nonneg (y + 4 : ℤ), sq_nonneg (x - 5 : ℤ), sq_nonneg ((x - y) : ℤ)]
  have h4 : y ≤ 9 := by
    nlinarith [sq_nonneg (x - 5 : ℤ), sq_nonneg (y - 4 : ℤ), sq_nonneg (x + y : ℤ),
            sq_nonneg (x - y : ℤ), sq_nonneg (x^2 - y^2 : ℤ), sq_nonneg (x * y), h1
           ]
  have h5 : x ≤ 14 := by
    nlinarith [h4, sq_nonneg (x - 5 : ℤ), sq_nonneg (y - 4 : ℤ), sq_nonneg (x + y : ℤ), sq_nonneg (x - y : ℤ),
            h1
           ]
  interval_cases x <;> interval_cases y <;> omega
  all_goals
    omega