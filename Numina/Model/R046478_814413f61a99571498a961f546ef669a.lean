import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_190207 (x : ℝ) (hx : x ≠ -8) :
    (x^3 - x^2 + x - 1) / (x + 8) ≤ 0 ↔ x ∈ Ioc (-8) 1 := by
  have h1 : (x^3 - x^2 + x - 1) = (x^2 + 1) * (x - 1) := by
    ring
  rw [h1] at *
  constructor
  · -- Assume (x^2 + 1) * (x - 1) / (x + 8) ≤ 0, prove x ∈ Ioc (-8) 1
    intro h
    have h2 : ((x ^ 2 + 1) * (x - 1)) / (x + 8) ≤ 0 := by simpa using h
    have h3 : ( (x ^ 2 + 1) * (x - 1) ≤ 0 ∧ x + 8 ≥ 0 ) ∨ ( (x ^ 2 + 1) * (x - 1) ≥ 0 ∧ x + 8 ≤ 0 ) := by
      apply div_nonpos_iff.1 at h2
      tauto
    rcases h3 with (h3 | h3)
    · -- Case 1 : (x ^ 2 + 1) * (x - 1) ≤ 0 ∧ x + 8 ≥ 0
      have h4 : (x - 1) ≤ 0 := by
        nlinarith [show x ^ 2 + 1 > 0 by nlinarith]
      have h5 : x - 1 ≤ 0 := by linarith
      have h5' : x ≤ 1 := by linarith
      have h6 : x + 8 ≥ 0 := by linarith [h3.2]
      have h7 : x > -8 := by
        by_contra h
        push_neg at h
        have h8 : x ≤ -8 := by linarith
        have h9 : x = -8 := by linarith
        exfalso
        exact hx (by linarith)
      constructor
      · -- Show that -8 < x
        linarith
      · -- Show that x ≤ 1
        linarith
    · -- Case 2 : (x ^ 2 + 1) * (x - 1) ≥ 0 ∧ x + 8 ≤ 0
      -- This case leads to a contradiction
      have h8 : (x - 1) ≥ 0 := by
        nlinarith [show x ^ 2 + 1 > 0 by nlinarith]
      have h9 : x - 1 ≥ 0 := by linarith
      have h9' : x ≥ 1 := by linarith
      have h10 : x + 8 ≤ 0 := by linarith [h3.2]
      -- Contradiction here, because x ≥ 1 and x ≤ -8
      -- 1 > 0. So, this part is not included that equality
      nlinarith
  · -- Assume x ∈ Ioc (-8) 1, prove (x^2 + 1) * (x - 1) / (x + 8) ≤ 0
    rintro ⟨h1, h2⟩
    have h3 : x + 8 > 0 := by linarith
    have h4 : x - 1 ≤ 0 := by linarith
    have h5 : (x ^ 2 + 1) * (x - 1) ≤ 0 := by
      nlinarith [show x ^ 2 + 1 > 0 by nlinarith]
    have h2 : ((x ^ 2 + 1) * (x - 1)) / (x + 8) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show that (x ^ 2 + 1) * (x - 1) ≤ 0
        linarith [h5]
      · -- Show that x + 8 ≥ 0
        linarith [h3]
    linarith [h2]