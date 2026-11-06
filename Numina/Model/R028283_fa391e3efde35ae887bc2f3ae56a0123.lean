import Mathlib

open Real Set
open scoped Real

theorem inequalities_99651 {a b c : ℝ} (x : ℝ) :
  (a + c) / 2 - sqrt ((a - c)^2 + b^2) / 2 ≤
  a * (cos x)^2 + b * cos x * sin x + c * (sin x)^2 ∧
  a * (cos x)^2 + b * cos x * sin x + c * (sin x)^2 ≤
  (a + c) / 2 + sqrt ((a - c)^2 + b^2) / 2 := by
  have h1 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
  have h2 : a * (cos x) ^ 2 + b * cos x * sin x + c * (sin x) ^ 2 =
      (a + c) / 2 + ( (a - c) / 2 ) * cos (2 * x) + (b / 2) * sin (2 * x) := by
    have hcos : cos (2 * x) = 2 * cos x ^ 2 - 1 := by
      rw [cos_two_mul]
    have hsin : sin (2 * x) = 2 * sin x * cos x := by
      rw [sin_two_mul]
    rw [hcos, hsin]
    ring_nf
    have h3 : sin x ^ 2 = 1 - cos x ^ 2 := by
      have h4 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
      linarith
    rw [h3]
    ring
  have h3 : ( (a - c) / 2 ) * cos (2 * x) + (b / 2) * sin (2 * x) ≤ Real.sqrt ((a - c)^2 + b^2) / 2 := by
    nlinarith [ Real.sqrt_nonneg ((a - c) ^ 2 + b ^ 2), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (a - c)^2 + b^2 by nlinarith), 
        sq_nonneg ( ( (a - c) / 2 ) * sin (2 * x) - (b / 2) * cos (2 * x) ), 
          Real.sin_sq_add_cos_sq (2 * x) ]
  have h4 : ( (a - c) / 2 ) * cos (2 * x) + (b / 2) * sin (2 * x) ≥ - Real.sqrt ((a - c)^2 + b^2) / 2 := by
    nlinarith [ Real.sqrt_nonneg ((a - c) ^ 2 + b ^ 2), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (a - c)^2 + b^2 by nlinarith), 
        sq_nonneg ( ( (a - c) / 2 ) * sin (2 * x) - (b / 2) * cos (2 * x) ), 
          Real.sin_sq_add_cos_sq (2 * x) ]
  constructor
  · -- Proof of the left inequality
    nlinarith [ h2, h3, Real.sqrt_nonneg ((a - c)^2 + b^2) ]
  · -- Proof of the right inequality
    nlinarith [ h2, h4, Real.sqrt_nonneg ((a - c)^2 + b^2) ]