import Mathlib

theorem algebra_120851 {a b c : ℝ} (ha : a + b + c > 0) (hb : a * b + b * c + c * a > 0)
    (hc : a * b * c > 0) : a > 0 ∧ b > 0 ∧ c > 0 := by

  have h1 : a > 0 := by
    by_contra h
    push_neg at h

    have h4 : b * c < 0 := by
      nlinarith [sq_nonneg (a), sq_nonneg (b - c), sq_nonneg (a + b + c), sq_nonneg (b), sq_nonneg (c), mul_self_nonneg (a - b), mul_self_nonneg (a - c), mul_self_nonneg (b - c)]

    nlinarith [sq_nonneg (b - c), sq_nonneg (a), sq_nonneg (b + c), sq_nonneg (a + b + c), mul_self_nonneg (b - c), mul_self_nonneg (a - b), mul_self_nonneg (a - c)]

  have h2 : b > 0 := by
    by_contra h
    push_neg at h

    have h5 : a * c < 0 := by
      nlinarith [sq_nonneg (b), sq_nonneg (a - c), sq_nonneg (a + b + c), sq_nonneg (a), sq_nonneg (c), mul_self_nonneg (a - b), mul_self_nonneg (b - c), mul_self_nonneg (a - c)]

    nlinarith [sq_nonneg (a - c), sq_nonneg (b), sq_nonneg (a + b + c), sq_nonneg (a + b + c), mul_self_nonneg (a - c), mul_self_nonneg (b - a), mul_self_nonneg (c - a)]

  have h3 : c > 0 := by
    by_contra h
    push_neg at h

    have h6 : a * b < 0 := by
      nlinarith [sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a + b + c), sq_nonneg (a), sq_nonneg (b), mul_self_nonneg (a - b), mul_self_nonneg (b - c), mul_self_nonneg (a - c)]

    nlinarith [sq_nonneg (a - b), sq_nonneg (c), sq_nonneg (a + b + c), sq_nonneg (a + b + c), mul_self_nonneg (a - b), mul_self_nonneg (c - a), mul_self_nonneg (c - b)]

  exact ⟨h1, h2, h3⟩