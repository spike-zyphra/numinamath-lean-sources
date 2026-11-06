import Mathlib

theorem algebra_10538 {x : ℝ} (hx : x ≠ 0) :
    (x^22 - 3 * x^5 + x^(-2 : ℤ) - 7) * (5 * x^4) = 5 * x^26 - 15 * x^9 - 35 * x^4 + 5 * x^2 := by
  have h1 : x^(-2 : ℤ) = 1 / (x^2 : ℝ) := by
    simp [zpow_neg, zpow_ofNat, hx]
  rw [h1]
  field_simp [hx]
  <;> ring