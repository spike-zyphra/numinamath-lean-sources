import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_155991 (f : ℝ → ℝ) (hf : f = tan) :
    ∀ x ∈ Ioo (-π/2) (π/2), deriv f x > 0 := by
  intro x hx
  rw [hf]
  rcases hx with ⟨h11, h12⟩
  have htan1 : deriv tan x = 1 / (cos x) ^ 2 := by
    rw [Real.deriv_tan]

  rw [htan1]

  have h5 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · -- Show -π / 2 < x
      linarith
    · -- Show x < π / 2
      linarith

  have htan2 : (cos x) ^ 2 > 0 := by
    nlinarith [h5]

  have pos1 : 1 / (cos x) ^ 2 > 0 := by
    apply one_div_pos.mpr
    linarith
  exact pos1