import Mathlib

theorem algebra_296284 {a : ℝ} (ha : ¬∃ x : ℝ, x^2 + 2 * a * x + 7 * a - 10 = 0) :
    ∃ x : ℝ, x^2 + 2 * a * x + 3 * a - 2 = 0 := by
  have h1 : (2 * a) ^ 2 - 4 * (7 * a - 10) < 0 := by
    by_contra h
    push_neg at h
    have h2 : ∃ x : ℝ, x ^ 2 + 2 * a * x + 7 * a - 10 = 0 := by
      have discriminant_nonneg : (2 * a) ^ 2 - 4 * (7 * a - 10) ≥ 0 := by linarith
      use (-2 * a + Real.sqrt ((2 * a) ^ 2 - 4 * (7 * a - 10))) / 2
      nlinarith [Real.sqrt_nonneg ((2 * a) ^ 2 - 4 * (7 * a - 10)), Real.sq_sqrt (show ((2 * a) ^ 2 - 4 * (7 * a - 10)) ≥ 0 by linarith)]
    contradiction

  have h3 : (2 * a) ^ 2 - 12 * a + 8 > 0 := by
    nlinarith [sq_nonneg (a - 2), sq_nonneg (a - 1), sq_nonneg (a - 5)]

  have h4 : ∃ x : ℝ, x^2 + 2 * a * x + 3 * a - 2 = 0 := by
    have h_pos : (2 * a) ^ 2 - 12 * a + 8 > 0 := h3
    use (-2 * a + Real.sqrt ((2 * a) ^ 2 - 12 * a + 8)) / 2
    nlinarith [Real.sqrt_nonneg ((2 * a) ^ 2 - 12 * a + 8), Real.sq_sqrt (show ( (2 * a) ^ 2 - 12 * a + 8) ≥ 0 by linarith)]
  exact h4