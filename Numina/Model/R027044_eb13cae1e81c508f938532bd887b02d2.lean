import Mathlib

theorem algebra_318142 (k : ℝ) (hk : k ≠ 0) :
    Set.Nonempty {x | x^2 - abs k = k * x} := by 
  have h1 : ∃ x, x ^ 2 - abs k = k * x := by
    by_cases h : k ≥ 0
    · -- Assume k ≥ 0, then |k| = k.
      have h2 : abs k = k := abs_of_nonneg h
      use (k + Real.sqrt (k ^ 2 + 4 * k)) / 2
      rw [h2]
      nlinarith [Real.sqrt_nonneg (k ^ 2 + 4 * k), Real.sq_sqrt (show k ^ 2 + 4 * k ≥ 0 by nlinarith)]
    · -- Assume k < 0
      have h : k < 0 := by linarith
      have h2 : abs k = -k := abs_of_neg h
      use (k + Real.sqrt (k ^ 2 - 4 * k)) / 2
      rw [h2]
      nlinarith [Real.sqrt_nonneg (k ^ 2 - 4 * k), Real.sq_sqrt (show k ^ 2 - 4 * k ≥ 0 by nlinarith [show k < 0 by linarith, sq_pos_of_ne_zero hk, sq_nonneg (k + 2)])]
  rcases h1 with ⟨x, hx⟩
  exact ⟨x, hx⟩