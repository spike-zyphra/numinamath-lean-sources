import Mathlib

theorem number_theory_192288 (x y : ℕ) : x^3 + y^3 + 1 = 3 * x * y ↔ (x = 1 ∧ y = 1) := by
  constructor
  · -- Assume the equation holds, prove (x = 1 ∧ y = 1)
    intro h
    have h1 : x ≤ y := by
      nlinarith [sq_nonneg (x - y : ℤ), sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 1 : ℤ),
        sq_nonneg (x - y : ℤ), sq_nonneg (x + y - 2 : ℤ)]
    have h2 : y ≤ x := by
      nlinarith [sq_nonneg (y - x : ℤ), sq_nonneg (x - 1 : ℤ), sq_nonneg (y - 1 : ℤ),
        sq_nonneg (x - y : ℤ), sq_nonneg (x + y - 2 : ℤ)]
    have h3 : x = y := by
      omega
    have h4 : x = 1 := by
      rw [show y = x by omega] at h
      have h5 : x ≤ 2 := by
        by_contra h6
        push_neg at h6
        have h8 : x ≥ 3 := by omega
        nlinarith [sq_nonneg ((x : ℤ) - 1), sq_nonneg ((x : ℤ) - 2), sq_nonneg ((x : ℤ) + 0),
          mul_nonneg (show (0 : ℤ) ≤ (x : ℤ) by omega) (show (0 : ℤ) ≤ (x : ℤ) by omega), 
          sq_nonneg ((x : ℤ) ^ 2 - 1)]
      interval_cases x <;> omega
    have h5 : y = 1 := by
      omega
    exact ⟨h4, h5⟩
  · -- Assume (x = 1 ∧ y = 1) holds, prove the equation
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    all_goals norm_num