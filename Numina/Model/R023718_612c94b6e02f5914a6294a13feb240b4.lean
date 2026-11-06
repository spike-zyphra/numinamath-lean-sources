import Mathlib

open Real
open scoped BigOperators

theorem inequalities_164256 (A B C : ℝ) (hA : A ∈ Set.Ioo 0 π)
  (hB : B ∈ Set.Ioo 0 π) (hC : C ∈ Set.Ioo 0 π) (hABC : A + B + C = π) :
  9 / Real.pi ≤ 1 / A + 1 / B + 1 / C ∧
  27 / Real.pi^2 ≤ 1 / A^2 + 1 / B^2 + 1 / C^2 := by
  rcases hA with ⟨hA1, hA2⟩
  rcases hB with ⟨hB1, hB2⟩
  rcases hC with ⟨hC1, hC2⟩
  constructor
  · -- First part: Prove $9/\pi \leq 1/A + 1/B + 1/C$.
    have h1 : 0 < A := hA1
    have h2 : 0 < B := hB1
    have h3 : 0 < C := hC1
    have h4 : A + B + C = π := hABC
    have h5 : 1 / A + 1 / B + 1 / C ≥ 9 / π := by 
      have h7 : 0 < π := Real.pi_pos
      have h8 : 0 < π * A * B * C := by positivity
      have h9 : (1 / A + 1 / B + 1 / C) - 9 / π ≥ 0 := by
        have h12 : (1 / A + 1 / B + 1 / C) - 9 / π = ( B * C * π + A * C * π + A * B * π - 9 * A * B * C ) / ( π * ( A * B * C ) ) := by
          field_simp
          ring
        rw [h12] at *
        apply div_nonneg 
        have h14 : B * C * π + A * C * π + A * B * π - 9 * A * B * C ≥ 0 := by 
          have h14' : π = A + B + C := by linarith
          rw [h14']
          nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (B - C), 
            mul_pos hA1 hB1, mul_pos hA1 hC1, mul_pos hB1 hC1, 
            sq_nonneg (A * B - B * C), sq_nonneg (B * C - C * A), sq_nonneg (C * A - A * B)
          ]
        linarith
        all_goals positivity
      linarith
    linarith
  · -- Second part (2): Prove that $27/ Real.pi^2 \leq 1/A^2+ 1/B^2+ 1/C^2$.
    have h1 : 0 < A := hA1
    have h2 : 0 < B := hB1
    have h3 : 0 < C := hC1
    have h4 : A + B + C = π := hABC
    have h5 : (1 / A^2 + 1 / B^2 + 1 / C^2) ≥ 27 / Real.pi^2 := by 
      have h7 : 0 < Real.pi := Real.pi_pos
      have h7' : 0 < Real.pi ^ 2 := by positivity
      have h8 : (1 / A^2 + 1 / B^2 + 1 / C^2) - 27 / Real.pi^2 ≥ 0 := by
        have h7 : 0 < Real.pi ^2 := by positivity
        have h8 : 0 < A^2 * B^2 * C^2 := by positivity
        have h11 : (1 / A^2 + 1 / B^2 + 1 / C^2) - 27 / Real.pi^2 = ( ( B^2 * C^2 * Real.pi^2 + A^2 * C^2 * Real.pi^2 + A^2 * B^2 * Real.pi^2 - 27 * (A * B * C) ^2 ) ) / ( Real.pi^2 * ( A^2 * B^2 * C^2 ) ) := by
          field_simp
          ring
        rw [h11] at *
        apply div_nonneg
        have h13 : B^2 * C^2 * Real.pi^2 + A^2 * C^2 * Real.pi^2 + A^2 * B^2 * Real.pi^2 - 27 * (A * B * C) ^2 ≥ 0 := by 
          have h14 : Real.pi = A + B + C := by linarith
          rw [h14]
          nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (B - C), 
            sq_nonneg (A * B - B * C), sq_nonneg (A * B - C * A), sq_nonneg (B * C - C * A), 
            mul_pos hA1 hB1, mul_pos hA1 hC1, mul_pos hB1 hC1, 
            mul_pos (show 0 < A * B by positivity) (show 0 < A * B by positivity), 
            mul_pos (show 0 < A * B by positivity) (show 0 < A * C by positivity), 
            mul_pos (show 0 < A * B by positivity) (show 0 < B * C by positivity)
          ]
        linarith
        all_goals positivity
      linarith
    linarith