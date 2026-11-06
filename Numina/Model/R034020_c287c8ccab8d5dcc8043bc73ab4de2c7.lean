import Mathlib

open Real

theorem inequalities_121771 (A B C : Real) (hA : A ∈ Set.Icc 0 π)
    (hB : B ∈ Set.Icc 0 π) (hC : C ∈ Set.Icc 0 π) (hABC : A + B + C = π)
    (x y z : ℝ) :
    x^2 + y^2 + z^2 ≥ 2 * x * y * cos C + 2 * y * z * cos A + 2 * z * x * cos B := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  have h1 : x ^ 2 + y ^ 2 + z ^ 2 - 2 * x * y * cos C - 2 * y * z * cos A - 2 * z * x * cos B ≥ 0 := by
    have h2 : A = π - (B + C) := by linarith
    have h3 : cos A = -cos (B + C) := by
      rw [h2]
      have h8 : cos (π - (B + C)) = -cos (B + C) := by
        rw [cos_pi_sub]
      linarith
    have h4 : cos (B + C) = cos B * cos C - sin B * sin C := by
      rw [cos_add]
    have h34 : (x - y * cos C - z * cos B) ^ 2 + (y * sin C - z * sin B) ^ 2 =
        x ^ 2 + y ^ 2 + z ^ 2 - 2 * x * y * cos C - 2 * y * z * cos A - 2 * z * x * cos B := by
      rw [h3, h4]
      ring_nf
      <;> simp [Real.cos_sq, Real.sin_sq]
      all_goals
        nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B, Real.sin_sq_add_cos_sq C,
          Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ B by linarith) (show B ≤ Real.pi by linarith),
          Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ C by linarith) (show C ≤ Real.pi by linarith),
          Real.sin_nonneg_of_nonneg_of_le_pi (show 0 ≤ B + C by nlinarith) (show B + C ≤ Real.pi by nlinarith)]
    have h18 : (x - y * cos C - z * cos B) ^ 2 + (y * sin C - z * sin B) ^ 2 ≥ 0 := by
      positivity
    nlinarith [h34, h18]
  linarith