import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_170589 (x : ℝ) (hx : x ≠ 0) :
  (x^2/8 + 3*x/4 + 3/2 + 1/x) * (1 - x - (x-2)^2 * (1 - x)/(x+2)^2) > 0 ↔
  x ∈ Ioo (-2) 0 ∪ Ioo 0 1 := by
  constructor
  · -- Assume the inequality is true, prove x in (-2,0) ∪ (0,1).
    intro h
    have h1 : x^2/8 + 3*x/4 + 3/2 + 1/x = ((x + 2) ^ 3) / (8 * x) := by 
      field_simp [hx]
      ring
    have h2 : 1 - x - (x-2)^2 * (1 - x)/(x+2)^2 = (8 * x * (1 - x)) / (x+2)^2 := by
      field_simp [(show x + 2 ≠ 0 by
        by_contra h'
        have h2 : x = -2 := by linarith
        rw [h2] at h 
        norm_num at h 
      )]
      ring
    rw [h1, h2] at h 
    have h4 : x + 2 ≠ 0 := by 
      by_contra h'
      have h2 : x = -2 := by linarith
      rw [h2] at h 
      norm_num at h 
    have h5 : ((x + 2) ^ 3 / (8 * x)) * (8 * x * (1 - x) / (x + 2) ^ 2) = (x + 2) * (1 - x) := by
      field_simp [show x ≠ 0 by simpa using hx, h4]
      <;> ring
    have h6 : (x + 2) * (1 - x) > 0 := by 
      linarith [h5, h]
    have h7 : -2 < x ∧ x < 1 := by 
      constructor
      · -- Solving to get -2 < x from (x + 2) * (1 - x) > 0.
        nlinarith
      · -- Solving to get x < 1 from (x + 2) * (1 - x) > 0.
        nlinarith
    by_cases h8 : x < 0
    · -- x < 0, so conclude x ∈ (-2,0)
      left
      constructor <;> nlinarith
    · -- Assume x > 0 since x ≠0 and x ≥0
      have h9 : x > 0 := by
        by_cases h2 : x > 0
        · linarith
        · have h2' : x = 0 := by 
            linarith [show x ≥ 0 from by nlinarith, h8]
          tauto
      right
      constructor <;> nlinarith
  · -- Assume x in (-2,0) ∪ (0,1), prove the inequality > 0.
    intro h
    rcases h with (h | h)
    · -- Assume x in (-2,0)
      rcases h with ⟨h1, h2⟩
      have h1 : x^2/8 + 3*x/4 + 3/2 + 1/x = ((x + 2) ^ 3) / (8 * x) := by 
        field_simp [hx]
        ring
      have h2' : 1 - x - (x-2)^2 * (1 - x)/(x+2)^2 = (8 * x * (1 - x)) / (x+2)^2 := by
        field_simp [(show x + 2 ≠ 0 by
          nlinarith
        )]
        ring
      rw [h1, h2']
      have h3 : -2 < x ∧ x < 0 := by
        tauto
      have h4 : x + 2 ≠ 0 := by linarith
      have h5 : ((x + 2) ^ 3 / (8 * x)) * (8 * x * (1 - x) / (x + 2) ^ 2) > 0 := by
        have h6 : ((x + 2) ^ 3 / (8 * x)) * (8 * x * (1 - x) / (x + 2) ^ 2) = (x + 2) * (1 - x) := by
          field_simp [show x ≠ 0 by assumption, h4]
          <;> ring
        have h7 : (x + 2) * (1 - x) > 0 := by
          nlinarith
        linarith
      linarith
    · -- Assume x in (0,1)
      rcases h with ⟨h1, h2⟩
      have h1 : x^2/8 + 3*x/4 + 3/2 + 1/x = ((x + 2) ^ 3) / (8 * x) := by 
        field_simp [hx]
        ring
      have h2' : 1 - x - (x-2)^2 * (1 - x)/(x+2)^2 = (8 * x * (1 - x)) / (x+2)^2 := by
        field_simp [(show x + 2 ≠ 0 by
          nlinarith
        )]
        ring
      rw [h1, h2']
      have h3 : 0 < x ∧ x < 1 := by
        tauto
      have h4 : x + 2 ≠ 0 := by linarith
      have h5 : ((x + 2) ^ 3 / (8 * x)) * (8 * x * (1 - x) / (x + 2) ^ 2) > 0 := by
        have h6 : ((x + 2) ^ 3 / (8 * x)) * (8 * x * (1 - x) / (x + 2) ^ 2) = (x + 2) * (1 - x) := by
          field_simp [show x ≠ 0 by assumption, h4]
          <;> ring
        have h7 : (x + 2) * (1 - x) > 0 := by
          nlinarith
        linarith
      linarith