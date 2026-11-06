import Mathlib

theorem algebra_2735 (y : ℝ → ℝ) (hy : y = fun x => x ^ 4 - 4 * x ^ 3 + 8 * x ^ 2 - 8 * x + 5) :
    Set.range y = {y | y ≥ 2} := by
  ext z
  simp [hy]
  constructor
  · -- Assume z in range of y
    rintro ⟨x, hx⟩
    have h1 : x ^ 4 - 4 * x ^ 3 + 8 * x ^ 2 - 8 * x + 5 ≥ 2 := by
      nlinarith [sq_nonneg (x ^ 2 - 2 * x ), sq_nonneg (x ^2 - 2 * x + 2), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2 - 4 * x + 2), sq_nonneg (x ^ 2 + x - 1)]
    linarith
  · -- Assume z >= 2
    intro hz
    use 1 + Real.sqrt (Real.sqrt (z - 1) - 1)
    nlinarith [Real.sqrt_nonneg (z - 1), Real.sqrt_nonneg (Real.sqrt (z - 1) - 1), Real.sq_sqrt (show (0 : ℝ) ≤ (z - 1) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ Real.sqrt (z - 1) - 1 by
      have h1 : Real.sqrt (z - 1) ≥ 1 := by
        have h2 : z - 1 ≥ (1 : ℝ) := by linarith
        have h3 : Real.sqrt (z - 1) ≥ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
        have h4 : Real.sqrt (1 : ℝ) = (1 : ℝ) := Real.sqrt_one
        nlinarith
      nlinarith
    ), sq_nonneg ( (1 + Real.sqrt (Real.sqrt (z - 1) - 1)) ^ 2 - 2 * (1 + Real.sqrt (Real.sqrt (z - 1) - 1)) + 1 ), sq_nonneg ( (1 + Real.sqrt (Real.sqrt (z - 1) - 1)) ^ 2 - 2 * (1 + Real.sqrt (Real.sqrt (z - 1) - 1)) + 2 ), sq_nonneg ( (1 + Real.sqrt (Real.sqrt (z - 1) - 1)) - 1 ) ]