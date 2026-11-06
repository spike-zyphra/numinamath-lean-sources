import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_185973 {k g : Set (ℝ × ℝ)}
  (hk : k = {(x, y) | y = (1/4)*x^2})
  (hg : g = {(x, -1)}) :
  k = {(x, y) | |y + 1| = sqrt (x^2 + (y - 1)^2)} := by

  rw [hk]
  ext ⟨x, y⟩
  simp [-one_div]
  constructor
  · -- First, show that if (x, y) ∈ k (i.e., y = (1/4)*x^2), then |y + 1| = sqrt (x^2 + (y - 1)^2)
    intro h
    have h1 : y = (1/4) * x^2 := by
      simpa using h
    rw [h1]
    have h2 : ((1 / 4) * x ^ 2 + 1) ≥ 0 := by
      nlinarith [sq_nonneg x]
    have h3 : |( (1 / 4) * x ^ 2 + 1 )| = ( (1 / 4) * x ^ 2 + 1 ) := by
      apply abs_of_nonneg
      linarith [h2]
    have h4 : sqrt (x ^ 2 + ( (1 / 4) * x ^ 2 - 1 ) ^ 2 ) = ( (1 / 4) * x ^ 2 + 1 ) := by
      have h5 : x ^ 2 + ( (1 / 4) * x ^ 2 - 1 ) ^ 2 = ( ( (1 / 4) * x ^ 2 + 1 ) ^ 2 ) := by
        nlinarith [sq_nonneg x]
      rw [h5]
      have h6 : sqrt ( ( (1 / 4) * x ^ 2 + 1 ) ^ 2 ) = ( (1 / 4) * x ^ 2 + 1 ) := by
        rw [Real.sqrt_sq]
        have h7 : ( (1 / 4) * x ^ 2 + 1 ) ≥ 0 := by
          nlinarith [sq_nonneg x]
        linarith
      linarith
    linarith [h3, h4]
  · -- Now prove the reverse direction
    intro h
    have h1 : |y + 1| = sqrt (x ^ 2 + (y - 1) ^ 2 ) := h
    have h3 : (y + 1) ^ 2 = (x ^ 2 + (y - 1) ^ 2 ) := by
      have h4 : |y + 1| ≥ 0 := abs_nonneg (y + 1)
      have h5 : sqrt (x ^ 2 + (y - 1) ^ 2 ) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + (y - 1) ^ 2 )
      have h6 : (|y + 1|) ^ 2 = ( sqrt (x ^ 2 + (y - 1) ^ 2 ) ) ^ 2 := by
        rw [h1]
      have h7 : (|y + 1|) ^ 2 = (y + 1) ^ 2 := by
        simp [abs_pow]
      have h8 : (sqrt (x ^ 2 + (y - 1) ^ 2 )) ^ 2 = (x ^ 2 + (y - 1) ^ 2 ) := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith [abs_nonneg (y + 1), Real.sqrt_nonneg (x ^ 2 + (y - 1) ^ 2 ), h7, h8]
    have h4 : y = (1 / 4) * x ^ 2 := by
      nlinarith [sq_nonneg (x), sq_nonneg (y - 1), sq_nonneg (y + 1), sq_nonneg (x - 0), sq_nonneg (y - 1) ]
    linarith [h4]