import Mathlib

open Real
open scoped Real

theorem inequalities_285483 (A B C : Real) (hA : A ∈ Set.Ioo 0 π)
  (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + B + C = π) :
  tan A ^ 2 + tan B ^ 2 + tan C ^ 2 ≥ tan A * tan B + tan B * tan C + tan C * tan A := by

  have h1 : (tan A - tan B) ^ 2 ≥ 0 := by
    exact sq_nonneg (tan A - tan B)
    
  have h2 : (tan B - tan C) ^ 2 ≥ 0 := by
    exact sq_nonneg (tan B - tan C)

  have h3 : (tan C - tan A) ^ 2 ≥ 0 := by
    exact sq_nonneg (tan C - tan A)

  have h6 : tan A ^ 2 + tan B ^ 2 + tan C ^ 2 - (tan A * tan B + tan B * tan C + tan C * tan A) = 
    (1 / 2) * ((tan A - tan B)^2 + (tan B - tan C)^2 + (tan C - tan A)^2) := by
      ring
      
  have h7 : (1 / 2) * ((tan A - tan B) ^ 2 + (tan B - tan C) ^ 2 + (tan C - tan A)^2) ≥ 0 := by
    linarith

  linarith [h6, h7]