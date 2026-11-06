import Mathlib

theorem algebra_9221 {x : ℤ} (A : ℤ) (hA : A = x^4 + 2*x^3 - x^2 - 5*x + 34) : ∃ m : ℤ, m^2 = A ↔ x = 11 := by
  use 131
  rw [show A = x ^ 4 + 2 * x ^ 3 - x ^ 2 - 5 * x + 34 by linarith [hA]]
  constructor
  · -- If 131² = x⁴ + 2x³ - x² - 5x + 34, then x = 11
    intro h
    have h1 : x ^ 4 + 2 * x ^ 3 - x ^ 2 - 5 * x + 34 = 17161 := by nlinarith
    have h2 : (x - 11) * (x^3 + 13*x^2 + 142*x + 1557) = 0 := by 
      nlinarith [h1]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- $x -11 =0$
      linarith
    · -- $x^3 +13x^2 +142x +1557 =0$
      have h5 : x^3 + 13*x^2 + 142*x + 1557 = 0 := by 
        nlinarith
      have h6 : x ≤ 28 := by
        nlinarith [sq_nonneg (x + 13), sq_nonneg (x * 0), sq_nonneg ((x + 0) ^ 2), sq_nonneg (x ^ 2), sq_nonneg ((x + 13) ^ 2)]
      have h7 : x ≥ -46 := by
        nlinarith [sq_nonneg (x + 13), sq_nonneg (x * 0), sq_nonneg ((x + 0) ^ 2), sq_nonneg (x ^ 2), sq_nonneg ((x + 13) ^ 2)]
      interval_cases x <;> omega
  · -- If x =11, then 131² = x⁴ + 2x³ -x² -5x +34
    intro h
    rw [show x = 11 by linarith]
    all_goals norm_num