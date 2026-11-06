import Mathlib

theorem algebra_143081 {p q b c : ℝ} (h1 : ¬∃ x : ℝ, x^2 + p * x + q = 0) (h2 : ¬∃ x : ℝ, x^2 + b * x + c = 0) :
    ¬∃ x : ℝ, 7 * x^2 + (2 * p + 3 * b + 4) * x + 2 * q + 3 * c + 2 = 0 := by
  rintro ⟨x, hx⟩
  have h3 : p ^ 2 < 4 * q := by
    by_contra h
    push_neg at h
    have h4 : ∃ x : ℝ, x ^ 2 + p * x + q = 0 := by
      use (-p + Real.sqrt (p ^ 2 - 4 * q)) / 2
      nlinarith [Real.sqrt_nonneg (p ^ 2 - 4 * q), Real.sq_sqrt (show 0 ≤ (p ^ 2 - 4 * q : ℝ) by nlinarith)]
    contradiction
  have h4 : b ^ 2 < 4 * c := by
    by_contra h
    push_neg at h
    have h5 : ∃ x : ℝ, x ^ 2 + b * x + c = 0 := by
      use (-b + Real.sqrt (b ^ 2 - 4 * c)) / 2
      nlinarith [Real.sqrt_nonneg (b ^ 2 - 4 * c), Real.sq_sqrt (show 0 ≤ (b ^ 2 - 4 * c : ℝ) by nlinarith)]
    contradiction
  nlinarith [sq_nonneg (x + (2 * p + 3 * b + 4) / 14), sq_nonneg (p - 2 * b), sq_nonneg (p + 2 * b), sq_nonneg (x * 7 + (2 * p + 3 * b + 4) / 2), sq_nonneg (p - b), sq_nonneg (p + b), sq_nonneg (x + 1)]