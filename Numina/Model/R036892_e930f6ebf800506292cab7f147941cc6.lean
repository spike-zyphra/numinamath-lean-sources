import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_190020 :
  {x : ℝ | (x^2 - 3 * x + 2) / (x^2 + 3 * x + 2) ≥ 1} = {x | x < -2 ∨ x ∈ Ioc (-1) 0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioc, not_false_iff]
  constructor
  · -- Assume (x^2 - 3 * x + 2) / (x^2 + 3 * x + 2) ≥ 1, prove x < -2 ∨ x ∈ Ioc (-1) 0
    intro h
    have h1 : x^2 + 3 * x + 2 ≠ 0 := by
      by_contra h2
      have h3 : (x + 1) * (x + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h3) with h4 h5
      · -- Case x + 1 = 0, so x = -1
        have h6 : x = -1 := by linarith
        rw [h6] at h
        norm_num at h
      · -- Case x + 2 = 0, so x = -2
        have h7 : x = -2 := by linarith
        rw [h7] at h
        norm_num at h
    have h2 : (x^2 - 3 * x + 2) / (x^2 + 3 * x + 2) ≥ 1 := h
    have h3 : x^2 + 3 * x + 2 > 0 ∨ x^2 + 3 * x + 2 < 0 := by
      by_contra h4
      push_neg at h4
      have h5 : x^2 + 3 * x + 2 = 0 := by
        linarith
      contradiction
    cases h3 with
    | inl h4 =>
      have h5 : x^2 - 3 * x + 2 ≥ x^2 + 3 * x + 2 := by
        apply (le_div_iff₀ h4).mp at h2
        linarith
      have h6 : x ≤ 0 := by
        nlinarith
      by_cases h7 : x < -2
      · left
        exact h7
      · -- Case x ≥ -2, but x ≤ 0, and denominator is positive
        have h8 : x ≥ -2 := by linarith
        have h9 : x > -1 := by
          nlinarith [sq_pos_of_ne_zero h1]
        right
        constructor
        · linarith
        · linarith
    | inr h4 =>
      have h5 : x^2 - 3 * x + 2 ≤ x^2 + 3 * x + 2 := by
        apply (le_div_iff_of_neg h4).mp at h2
        linarith
      have h6 : x ≥ 0 := by
        nlinarith
      nlinarith
  · -- Assume x < -2 ∨ x ∈ Ioc (-1) 0, prove (x^2 - 3 * x + 2) / (x^2 + 3 * x + 2) ≥ 1
    rintro (h | ⟨h1, h2⟩)
    · -- Case x < -2
      have h3 : x^2 + 3 * x + 2 > 0 := by
        nlinarith
      have h4 : x^2 - 3 * x + 2 ≥ x^2 + 3 * x + 2 := by
        nlinarith
      apply (le_div_iff₀ h3).mpr
      linarith
    · -- Case x ∈ Ioc (-1) 0
      have h3 : x^2 + 3 * x + 2 > 0 := by
        nlinarith
      have h4 : x^2 - 3 * x + 2 ≥ x^2 + 3 * x + 2 := by
        nlinarith
      apply (le_div_iff₀ h3).mpr
      linarith