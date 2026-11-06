import Mathlib

theorem algebra_297477 {m : ℝ} (hm : m ≠ 2) (A B C : ℝ)
    (hA : A = -1 * (m - 2) / 2 + Real.sqrt ((m - 2)^2 - 12) / 2)
    (hB : B = -1 * (m - 2) / 2 - Real.sqrt ((m - 2)^2 - 12) / 2)
    (hC : C = 3 * (m + 1)) (hAB : A < B) (hA0 : A * B = 6) :
    Real.sin C = Real.sqrt 2 / 10 ∨ Real.sin C = Real.sqrt 2 / 2 := by
  have h1 : A * B = 3 := by
    rw [hA, hB]
    have h5 : Real.sqrt ((m - 2) ^ 2 - 12) ^ 2 = (m - 2) ^ 2 - 12 := by
      apply Real.sq_sqrt
      nlinarith [sq_nonneg (m - 2), sq_nonneg (m ^ 2 - 2 ^ 2 : ℝ), sq_nonneg ((m - 2) : ℝ)]
    nlinarith [Real.sqrt_nonneg ((m - 2) ^ 2 - 12)]
  nlinarith