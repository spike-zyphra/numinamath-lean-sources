import Mathlib

open Real
open scoped BigOperators

theorem inequalities_597050 (A B C : ℝ) (hA : A ∈ Set.Ioo 0 π)
  (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + B + C = π)
  (x y z : ℝ) :
  x^2 + y^2 + z^2 - 2 * x * y * cos C - 2 * y * z * cos A - 2 * z * x * cos B ≥ 0 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with  ⟨hB1, hB2⟩
  rcases hC with  ⟨hC1, hC2⟩
  have h1 : cos A = -cos (B + C) := by
    have h2 : A = π - (B + C) := by linarith [hABC]
    rw [h2]
    have h3 : cos (π - (B + C)) = -cos (B + C) := by
      rw [cos_pi_sub]
    linarith
  have h2 : x ^ 2 + y ^ 2 + z ^ 2 - 2 * x * y * cos C - 2 * y * z * cos A - 2 * z * x * cos B =
      (x - y * cos C - z * cos B) ^ 2 + (y * sin C - z * sin B) ^ 2 := by 
    rw [show cos A = -cos (B + C) by linarith [h1]]
    have h4 : cos (B + C) = cos B * cos C - sin B * sin C := by
      rw [Real.cos_add]
    rw [h4]
    ring_nf
    <;> simp [Real.sin_sq, Real.cos_sq]
    <;> nlinarith
  rw [h2]
  positivity