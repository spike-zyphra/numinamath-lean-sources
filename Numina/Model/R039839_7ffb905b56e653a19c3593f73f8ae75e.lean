import Mathlib

theorem algebra_18869 (m : ℝ) (h : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ 2*x1^2+m*x1+8=0 ∧ 2*x2^2+m*x2+8=0) :
    m < -8 ∨ m > 8 := by
  rcases h with ⟨x1, x2, hx12, h1, h2⟩
  have h3 : 2 * x1^2 + m * x1 + 8 = 0 := by linarith
  have h4 : 2 * x2^2 + m * x2 + 8 = 0 := by linarith
  have h5 : 2 * (x1^2 - x2^2) + m * (x1 - x2) = 0 := by
    linarith [h3, h4]
  have h6 : (x1 - x2) * (2 * (x1 + x2) + m) = 0 := by
    ring_nf at h5 ⊢
    linarith
  cases' (mul_eq_zero.mp h6) with h7 h8
  · -- Case where `x1 - x2 = 0`.
    exfalso
    apply hx12
    linarith
  · -- Case where `2 * (x1 + x2) + m = 0`.
    have h8' : m = -2 * (x1 + x2) := by linarith
    have h11 : m ^ 2 > 64 := by
      have h9 : (x1 - x2) ≠ 0 := by
        intro h
        apply hx12
        linarith
      have h10 : (x1 - x2) ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        exact h9
      nlinarith [sq_pos_of_ne_zero (show (x1 - x2) ≠ 0 by intro h; apply hx12; linarith),
                sq_nonneg (x1 + x2),
                sq_nonneg (x1 - x2),
                sq_nonneg (x1 - x2),
                sq_nonneg (m + 2 * (x1 + x2))
          ]
    by_contra h
    push_neg at h
    nlinarith