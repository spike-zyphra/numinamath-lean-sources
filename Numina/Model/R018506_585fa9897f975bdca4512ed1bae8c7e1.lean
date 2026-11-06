import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_199138 (x y : Fin 3 → ℝ)
  (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
  2018 ≤
  sqrt ((2018 - y 0 - y 1 - y 2)^2 + x 2^2) +
  sqrt (y 2^2 + x 1^2) +
  sqrt (y 1^2 + x 0^2) +
  sqrt (y 0^2 + (x 0 + x 1 + x 2)^2) := by 
  have h2 : sqrt ((2018 - y 0 - y 1 - y 2) ^ 2 + x 2 ^ 2) ≥ abs (2018 - y 0 - y 1 - y 2) := by
    have h3 : (2018 - y 0 - y 1 - y 2) ^ 2 + x 2 ^ 2 ≥ (2018 - y 0 - y 1 - y 2) ^ 2 := by
      linarith [sq_nonneg (x 2)]
    have h4 : sqrt ((2018 - y 0 - y 1 - y 2) ^ 2 + x 2 ^ 2) ≥ sqrt ((2018 - y 0 - y 1 - y 2) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    have h5 : sqrt ((2018 - y 0 - y 1 - y 2) ^ 2) = abs (2018 - y 0 - y 1 - y 2) := by
      rw [Real.sqrt_sq_eq_abs]
    linarith [h4, h5]
  have h3 : sqrt (y 2 ^ 2 + x 1 ^ 2) ≥ abs (y 2) := by
    have h4 : y 2 ^ 2 + x 1 ^ 2 ≥ y 2 ^ 2 := by
      linarith [sq_nonneg (x 1)]
    have h5 : sqrt (y 2 ^ 2 + x 1 ^ 2) ≥ sqrt (y 2 ^ 2) := Real.sqrt_le_sqrt (by linarith)
    have h6 : sqrt (y 2 ^ 2) = abs (y 2) := by
      rw [Real.sqrt_sq_eq_abs]
    linarith [h5, h6]
  have h4 : sqrt (y 1 ^ 2 + x 0 ^ 2) ≥ abs (y 1) := by
    have h5 : y 1 ^ 2 + x 0 ^ 2 ≥ y 1 ^ 2 := by
      linarith [sq_nonneg (x 0)]
    have h6 : sqrt (y 1 ^ 2 + x 0 ^ 2) ≥ sqrt (y 1 ^ 2) := Real.sqrt_le_sqrt (by linarith)
    have h7 : sqrt (y 1 ^ 2) = abs (y 1) := by
      rw [Real.sqrt_sq_eq_abs]
    linarith [h6, h7]
  have h5 : sqrt (y 0 ^ 2 + (x 0 + x 1 + x 2) ^ 2) ≥ abs (y 0) := by
    have h6 : y 0 ^ 2 + (x 0 + x 1 + x 2) ^ 2 ≥ y 0 ^ 2 := by
      linarith [sq_nonneg (x 0 + x 1 + x 2)]
    have h7 : sqrt (y 0 ^ 2 + (x 0 + x 1 + x 2) ^ 2) ≥ sqrt (y 0 ^ 2) := Real.sqrt_le_sqrt (by linarith)
    have h8 : sqrt (y 0 ^ 2) = abs (y 0) := by
      rw [Real.sqrt_sq_eq_abs]
    linarith [h7, h8]
  have h6 : sqrt ((2018 - y 0 - y 1 - y 2) ^ 2 + x 2 ^ 2) + sqrt (y 2 ^ 2 + x 1 ^ 2) + sqrt (y 1 ^ 2 + x 0 ^ 2) + sqrt (y 0 ^ 2 + (x 0 + x 1 + x 2) ^ 2) ≥ abs (2018 - y 0 - y 1 - y 2) + abs (y 2) + abs (y 1) + abs (y 0) := by
    linarith [h2, h3, h4, h5]
  have h7 : abs (2018 - y 0 - y 1 - y 2) + abs (y 2) + abs (y 1) + abs (y 0) ≥ 2018 := by
    cases' abs_cases (2018 - y 0 - y 1 - y 2) with h h <;> 
      cases' abs_cases (y 2) with h2 h2 <;> 
        cases' abs_cases (y 1) with h1 h1 <;> 
          cases' abs_cases (y 0) with h0 h0 <;> 
            all_goals
              linarith
  linarith [h6, h7]