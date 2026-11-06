import Mathlib

open Real
open scoped BigOperators

theorem inequalities_104499 (A B C : Real) (hA : A ∈ Set.Ioo 0 π)
  (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + B + C = π)
  (x y z : ℝ) :
  x^2 + y^2 + z^2 ≥ 2 * x * y * cos C + 2 * y * z * cos A + 2 * z * x * cos B := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  have h1 : C = π - (A + B) := by linarith 
  have h2 : cos C = -cos (A + B) := by 
    rw [h1]
    rw [cos_pi_sub]
  have h3 : cos (A + B) = cos A * cos B - sin A * sin B := by 
    rw [cos_add]
  have h4 : cos C = - (cos A * cos B - sin A * sin B) := by 
    rw [h2, h3]
  have h5 : cos C = -cos A * cos B + sin A * sin B := by 
    linarith [h4]
  have eq1 : x^2 + y^2 + z^2 - (2 * x * y * cos C + 2 * y * z * cos A + 2 * z * x * cos B) =
    (y * cos C + z * cos B - x) ^ 2 + (y * sin C - z * sin B) ^ 2 := by 
    rw [show cos C = -cos A * cos B + sin A * sin B by linarith [h5]]
    have h11 : sin C = sin (A + B) := by 
      have : C = π - (A + B) := by linarith 
      rw [this]
      rw [sin_pi_sub]
    have h12 : sin (A + B) = sin A * cos B + cos A * sin B := by 
      rw [sin_add]
    rw [h11, h12]
    ring_nf
    <;> simp [sin_sq, cos_sq] <;> ring
  have eq2 : (y * cos C + z * cos B - x) ^ 2 + (y * sin C - z * sin B) ^ 2 ≥ 0 := by 
    positivity
  linarith [eq1, eq2]