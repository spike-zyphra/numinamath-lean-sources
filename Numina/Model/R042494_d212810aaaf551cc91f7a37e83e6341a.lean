import Mathlib

theorem algebra_276595 {k : ℝ} (h : ∃ x1 x2, x1 ≠ x2 ∧ (k^2 - 5 * k + 3) * x1^2 + (3 * k - 1) * x1 + 2 = 0 ∧
    (k^2 - 5 * k + 3) * x2^2 + (3 * k - 1) * x2 + 2 = 0 ∧ x1 / x2 = 2) :
    k = 2 / 3 := by
  rcases h with ⟨x1, x2, hx12, h1, h2, h3⟩
  have hx2_ne_zero : x2 ≠ 0 := by
    by_contra h'
    rw [h'] at h3
    norm_num at h3
  have h4 : x1 = 2 * x2 := by
    have hne : x2 ≠ 0 := hx2_ne_zero
    field_simp [hne] at h3
    linarith
  rw [h4] at h1
  have h5 : (k^2 - 5 * k + 3) * (2 * x2) ^ 2 + (3 * k - 1) * (2 * x2) + 2 = 0 := by
    linarith
  have h6 : (k^2 - 5 * k + 3) * x2 ^ 2 + (3 * k - 1) * x2 + 2 = 0 := by
    linarith
  have h7 : 3 * (k^2 - 5 * k + 3) * x2 ^ 2 + (3 * k - 1) * x2 = 0 := by
    nlinarith [h5, h6]
  have h8 : x2 * (3 * (k^2 - 5 * k + 3) * x2 + (3 * k - 1)) = 0 := by
    linarith [h7]
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- x2 = 0 is not a valid solution
    exfalso
    apply hx2_ne_zero
    linarith
  · -- 3*(k^2 - 5*k + 3)*x2 + (3*k - 1) = 0
    nlinarith [sq_pos_of_ne_zero (show k^2 - 5*k + 3 ≠ 0 by
      by_contra h'
      have h8 : (k^2 - 5 * k + 3) = 0 := by linarith [h']
      rw [h8] at h6
      nlinarith [sq_pos_of_ne_zero (show x2 ≠ 0 by exact hx2_ne_zero), sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
        intro h'
        apply hx12
        nlinarith
      )]
    ), sq_pos_of_ne_zero (show x2 ≠ 0 by exact hx2_ne_zero)]