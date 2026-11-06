import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_189978 (x : ℝ) :
  (x ∈ Ioo (-3) 1 ∧ sqrt (17 - 15 * x - 2 * x ^ 2) / (x + 3) > 0) ↔
  (x ∈ Ioo (-3) 1) := by
  constructor
  · -- Forward direction: if (x ∈ (-3,1) ∧ sqrt/(x+3) >0), then x ∈ (-3,1)
    rintro ⟨h, hs⟩
    tauto
  · -- Backward direction: if x ∈ (-3,1), proving (x ∈ (-3,1) ∧ sqrt/(x+3) >0)
    intro h
    constructor
    · -- Original assumption
      exact h
    · -- Prove sqrt(17 -15 * x -2 *x^2) / (x + 3) >0
      rcases h with ⟨h1, h2⟩
      have h3 : -3 < x := h1
      have h4 : x < 1 := h2
      have h5 : 17 - 15 * x - 2 * x ^ 2 > 0 := by
        nlinarith
      have h6 : sqrt (17 - 15 * x - 2 * x ^ 2) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have h7 : x + 3 > 0 := by
        linarith
      apply div_pos
      exact h6
      linarith