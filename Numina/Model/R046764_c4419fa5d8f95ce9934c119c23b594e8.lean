import Mathlib

theorem algebra_324337 (f : ℝ → ℝ) (m : ℝ) (hm : m > 0)
    (hf : ∀ x, f x = x ^ 2 + x + m) (t : ℝ) (ht : f t < 0) :
    ∃ x, x ∈ Set.Ioo t (t + 1) ∧ f x = 0 := by
  have h1 : t ^ 2 + t + m < 0 := by
    have ht' : f t < 0 := ht
    rw [hf t] at ht'
    linarith

  by_cases h2 : 1 - 4 * m ≥ 0
  · -- Case where the discriminant is non-negative.
    have h3 : (1 - 4 * m : ℝ) ≥ 0 := h2
    use (-1 + Real.sqrt (1 - 4 * m)) / 2
    constructor
    · -- Show that ( (-1 + Real.sqrt (1 - 4 * m)) / 2 ) ∈ (t, t + 1)
      constructor
      · -- Show that t < ( (-1 + Real.sqrt (1 - 4 * m)) / 2 )
        nlinarith [ Real.sqrt_nonneg (1 - 4 * m), Real.sq_sqrt (show (1 - 4 * m : ℝ) ≥ 0 by linarith), sq_pos_of_pos hm, sq_nonneg (t + 1 / 2), sq_nonneg (t - (-1 + Real.sqrt (1 - 4 * m)) / 2) ]
      · -- Show that ( (-1 + Real.sqrt (1 - 4 * m)) / 2 ) < t + 1
        nlinarith [ Real.sqrt_nonneg (1 - 4 * m), Real.sq_sqrt (show (1 - 4 * m : ℝ) ≥ 0 by linarith), sq_pos_of_pos hm, sq_nonneg (t + 1 / 2), sq_nonneg (t - (-1 + Real.sqrt (1 - 4 * m)) / 2) ]
    · -- Show that f((-1 + Real.sqrt (1 - 4 * m)) / 2 ) = 0
      rw [hf]
      nlinarith [ Real.sqrt_nonneg (1 - 4 * m), Real.sq_sqrt (show (1 - 4 * m : ℝ) ≥ 0 by linarith) ]
  · -- Case where the discriminant is negative.
    have h3 : (1 - 4 * m : ℝ) < 0 := by linarith
    nlinarith [ sq_nonneg (t + 1 / 2), sq_nonneg (4 * t + 2) ]