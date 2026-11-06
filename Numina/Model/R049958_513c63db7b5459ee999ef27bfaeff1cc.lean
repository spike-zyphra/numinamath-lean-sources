import Mathlib

theorem algebra_99535 (A B C : Real) (h₀ : A ∈ Set.Ioo 0 π)
    (h₁ : B ∈ Set.Ioo 0 π) (h₂ : C ∈ Set.Ioo 0 π) (h₃ : A + B + C = π)
    (h₄ : (Real.sin A + Real.sin B + Real.sin C) / (Real.cos A + Real.cos B + Real.cos C) = 12 / 7)
    (h₅ : Real.sin A * Real.sin B * Real.sin C = 12 / 25) :
    100 * Real.sin A * Real.sin B * Real.sin C = 48 := by
  linarith [h₅]