import Mathlib

theorem number_theory_198906 (z : ℤ) (h : z^3 = 456533) : z = 77 := by
  have h4 : z ≤ 77 := by
    by_contra h4
    push_neg at h4
    have h5 : z ≥ 78 := by
      omega
    nlinarith [sq_nonneg (z - 78), sq_nonneg (z + 78), sq_nonneg (z - 77), sq_nonneg (z + 77), sq_nonneg (z^2 - 5929), sq_nonneg (z - 77), sq_nonneg (z + 77)]
  have h5 : z ≥ 77 := by
    by_contra h5
    push_neg at h5
    have h6 : z ≤ 76 := by
      omega
    nlinarith [sq_nonneg (z - 76), sq_nonneg (z + 76), sq_nonneg (z - 77), sq_nonneg (z + 77), sq_nonneg (z^2 - 5929), sq_nonneg (z - 77), sq_nonneg (z + 77)]
  have h6 : z = 77 := by
    linarith
  exact h6