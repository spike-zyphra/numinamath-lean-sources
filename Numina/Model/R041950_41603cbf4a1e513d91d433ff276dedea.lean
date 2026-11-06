import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_285683 {R m : ℝ} (hR : R > 0) (hm : m > 0) (hm_R : m ≤ 2*R) :
    IsGreatest {V | ∃ d₁ d₂, d₁ < d₂ ∧ d₂ - d₁ = m ∧ R^2 - d₁^2 ≥ 0 ∧ R^2 - d₂^2 ≥ 0 ∧
      V = (π/6) * m^3 + (π/2) * m * ((R^2 - d₁^2) + (R^2 - d₂^2))} 
    (π * m * R^2 - (π/12) * m^3) := by
  constructor
  · -- Show that `π * m * R^2 - (π/12) * m^3` is in the set.
    use -m / 2, m / 2
    constructor
    · -- Show that -m/2 < m/2
      linarith
    constructor
    · -- Show that m / 2 - (-m / 2) = m
      ring
    constructor
    · -- Show that R^2 - (-m / 2) ^ 2 ≥ 0
      have h1 : R ^ 2 - (-m / 2) ^ 2 ≥ 0 := by
        nlinarith [ sq_nonneg (R ^ 2 - m ^ 2 / 4), sq_nonneg (m - 2 * R), hR, hm, hm_R, sq_nonneg (R) ]
      exact h1
    constructor
    · -- Show that R^2 - (m / 2) ^ 2 ≥ 0
      have h1 : R ^ 2 - (m / 2) ^ 2 ≥ 0 := by
        nlinarith [ sq_nonneg (R ^ 2 - m ^ 2 / 4), sq_nonneg (m - 2 * R), hR, hm, hm_R, sq_nonneg (R) ]
      exact h1
    · -- Show the equality of the volume
      field_simp
      ring
  · -- Show that `π * m * R^2 - (π/12) * m^3` is the greatest in the set.
    intro V h
    rcases h with ⟨d₁, d₂, h1, h2, h3, h4, hV⟩
    have h5 : m ^ 2 ≤ 2 * (d₁ ^ 2 + d₂ ^ 2) := by
      have eq1 : d₂ - d₁ = m := by linarith
      have eq2 : d₂ = d₁ + m := by linarith
      rw [eq2]
      nlinarith [ sq_nonneg (d₁ + (d₁ + m) ), sq_nonneg (d₁ - (d₁ + m) ) ]
    have h6 : (π / 6) * m ^ 3 + (π / 2) * m * ((R ^ 2 - d₁ ^ 2) + (R ^ 2 - d₂^2)) ≤ π * m * R^2 - (π / 12) * m ^ 3 := by
      have h7 : (R ^ 2 - d₁ ^ 2) + (R ^ 2 - d₂ ^ 2) = 2 * R ^ 2 - (d₁ ^ 2 + d₂ ^ 2) := by ring
      rw [h7] at *
      nlinarith [ sq_nonneg (R ^ 2 - m ^ 2 / 4), sq_nonneg (m - 2 * R), sq_nonneg (d₁ + d₂), sq_nonneg (d₁ - d₂), sq_nonneg (d₁ - (-m / 2)), sq_nonneg (d₂ - (m / 2)), h5, mul_pos (show 0 < π by positivity) (show 0 < π by positivity), hR, hm, hm_R, h3, h4, mul_pos hR hm, mul_pos (show 0 < π by positivity) hR, mul_pos (show 0 < π by positivity) hm ]
    linarith [ hV, h6 ]