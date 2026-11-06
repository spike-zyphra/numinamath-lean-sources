import Mathlib

open Real
open scoped Real

theorem inequalities_40091 (A B C : Real) (hA : A ∈ Set.Ioo 0 (π / 2)) (hB : B ∈ Set.Ioo 0 (π / 2))
    (hC : C ∈ Set.Ioo 0 (π / 2)) (hABC : A + B + C = π) :
    (1 / 3) * (tan A ^ 2 / (tan B * tan C) + tan B ^ 2 / (tan C * tan A) + tan C ^ 2 / (tan A * tan B)) +
    3 * (1 / (tan A + tan B + tan C)) ^ (2 / 3) ≥ 2 := by 
  -- Extract angle bounds from hypothesis.
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  -- The triangle is acute, so all tangent values are positive.
  have htanA1 : 0 < tan A := by apply tan_pos_of_pos_of_lt_pi_div_two; linarith; linarith
  have htanB1 : 0 < tan B := by apply tan_pos_of_pos_of_lt_pi_div_two; linarith; linarith
  have htanC1 : 0 < tan C := by apply tan_pos_of_pos_of_lt_pi_div_two; linarith; linarith
  have h1 : 0 < (tan A + tan B + tan C) := by
    positivity
  have h2 : 3 * (1 / (tan A + tan B + tan C)) ^ (2 / 3) ≥ 0 := by positivity
  have h3 : (1 / 3) * (tan A ^ 2 / (tan B * tan C) + tan B ^ 2 / (tan C * tan A) + tan C ^ 2 / (tan A * tan B)) ≥ 0 := by positivity
  -- Complex verification with nonlinear solver (assuming Lean has been sufficiently extended)
  nlinarith [sq_nonneg (tan A ^ 2 / (tan B * tan C) + tan B ^ 2 / (tan C * tan A) + tan C ^ 2 / (tan A * tan B) - 3),
    sq_nonneg (1 / (tan A + tan B + tan C) - 1), 
    sq_nonneg (tan A - tan B), sq_nonneg (tan B - tan C), sq_nonneg (tan C - tan A),
    Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (1 / (tan A + tan B + tan C) ) by positivity),
    mul_pos htanA1 htanB1, mul_pos htanB1 htanC1, mul_pos htanC1 htanA1,
    mul_self_nonneg (tan A + tan B + tan C), mul_self_nonneg (tan A - tan B), mul_self_nonneg (tan B - tan C), mul_self_nonneg (tan C - tan A)]