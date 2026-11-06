import Mathlib

theorem inequalities_308233 (p q x y : ℝ) (h₀ : 0 < p) (h₁ : p ≤ x) (h₂ : x ≤ y) (h₃ : y ≤ q) :
    x / y + y / x ≤ p / q + q / p := by 
  have h4 : 0 < y := by linarith
  have h5 : 0 < x := by linarith
  have h6 : 0 < q := by linarith
  have h7 : 0 < x * y := by positivity
  have h8 : 0 < p * q := by positivity
  have h9 : 0 < x * y * p * q := by positivity
  have h10 : x / y + y / x - (p / q + q / p) ≤ 0 := by
    have h11 : x / y + y / x - (p / q + q / p) =
        ( (x^2 + y^2) * (p * q) - (p^2 + q^2) * (x * y) ) / (x * y * p * q) := by
      field_simp
      ring
    have h12 : (x^2 + y^2) * (p * q) - (p^2 + q^2) * (x * y) ≤ 0 := by
      nlinarith [sq_nonneg (x * q - y * p), sq_nonneg (x * p - y * q), 
          mul_nonneg (show (0 : ℝ) ≤ x - p by linarith) (show (0 : ℝ) ≤ y - x by linarith),
          mul_nonneg (show (0 : ℝ) ≤ y - x by linarith) (show (0 : ℝ) ≤ q - y by linarith),
          mul_pos h₀ h6, 
          sq_nonneg (x - y), 
          sq_nonneg (p - q)]
    have h13 : ( (x^2 + y^2) * (p * q) - (p^2 + q^2) * (x * y) ) / (x * y * p * q) ≤ (0 : ℝ) := by
      apply div_nonpos_of_nonpos_of_nonneg h12 (by positivity)
    linarith [h11, h13]
  linarith