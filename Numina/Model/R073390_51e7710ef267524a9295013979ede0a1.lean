import Mathlib

theorem algebra_186402 {a q : ℝ} (hq : |q| < 1) (hsum : a / (1 - q) = 8 / 5)
    (hsecond : a * q = -1 / 2) : a * q^2 = 1 / 8 := by
  have hq1 : q ≠ 1 := by
    by_contra h
    rw [h] at hsum hq
    norm_num at hsum hq
    all_goals linarith [abs_lt.mp hq]

  have h_eq1 : a = (8 / 5) * (1 - q) := by
    have h1 : 1 - q ≠ 0 := by
      intro h2
      apply hq1
      linarith
    field_simp [h1] at hsum ⊢
    linarith

  rw [h_eq1] at hsecond

  have hq2 : q = -1/4 := by
    have h1 : 8 * q ^2 - 8 * q - 5/2 = 0 := by
      nlinarith

    have h2 : (4 * q - 5) * (4 * q + 1) = 0 := by
      nlinarith

    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- Case 1: $\ln\ 4 \cdot q - 5 = 0$
      have hq_eq : q = 5/4 := by linarith
      have h_abs_q : |q| ≥ 1 := by
        rw [hq_eq]
        norm_num [abs_of_nonneg]
        all_goals linarith
      linarith [abs_lt.mp hq, h_abs_q]
    · -- Case 2: $\ln\ 4 \cdot q + 1 = 0$
      linarith

  have h_eq2 : a = 2 := by
    rw [hq2] at h_eq1
    linarith

  rw [h_eq2, hq2]
  norm_num