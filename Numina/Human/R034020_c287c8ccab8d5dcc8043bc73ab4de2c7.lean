import Mathlib

open Real

theorem inequalities_121771 (A B C : Real) (hA : A ∈ Set.Icc 0 π)
    (hB : B ∈ Set.Icc 0 π) (hC : C ∈ Set.Icc 0 π) (hABC : A + B + C = π)
    (x y z : ℝ) :
    x^2 + y^2 + z^2 ≥ 2 * x * y * cos C + 2 * y * z * cos A + 2 * z * x * cos B := by 
  -- `left - right = (x - y * cos C - z * cos B) ^ 2 + (y * sin C - z * sin B) ^ 2`
  have h1 : x ^ 2 + y ^ 2 + z ^ 2 - 2 * x * y * cos C - 2 * y * z * cos A - 2 * z * x * cos B ≥ 0 := by
    have h2 : (x - y * cos C - z * cos B) ^ 2 + (y * sin C - z * sin B) ^ 2 ≥ 0 := by
      apply add_nonneg
      · apply sq_nonneg
      · apply sq_nonneg
    have h3 : (x - y * cos C - z * cos B) ^ 2 + (y * sin C - z * sin B) ^ 2 = 
        x^2 + y^2 + z^2 - 2 * x * y * cos C - 2 * y * z * cos A - 2 * z * x * cos B := by
      ring_nf
      have h4 : cos A = -cos (B + C) := by
        rw [show A = π - (B + C) by linarith [hABC]]
        rw [cos_pi_sub]
      rw [h4]
      have h5 : cos (B + C) = cos B * cos C - sin B * sin C := by
        exact cos_add B C
      rw [h5]
      simp [mul_assoc]
      <;> nlinarith [Real.cos_sq_add_sin_sq B, Real.cos_sq_add_sin_sq C]
    linarith
  linarith