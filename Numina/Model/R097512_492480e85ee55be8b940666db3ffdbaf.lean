import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_230194 (x : ℝ) :
  x ≠ 0 ∧ x ≠ 1 ∧ 1 / (1 - 1 / (1 + 1 / (x - 1))) ≤ 2019 ↔
  x ≤ 2019 ∧ x ≠ 0 ∧ x ≠ 1 := by
  constructor
  · -- Assume left side: x ≠ 0 ∧ x ≠ 1 ∧ 1 / (1 - 1 / (1 + 1 / (x - 1))) ≤ 2019, prove x ≤ 2019 ∧ x ≠ 0 ∧ x ≠ 1
    intro h
    rcases h with ⟨hx1, hx2, hineq⟩
    have h1 : 1 / (1 - 1 / (1 + 1 / (x - 1))) = x := by
      have h2 : x - 1 ≠ 0 := by
        intro h'
        apply hx2
        linarith
        all_goals linarith
      have h4 : 1 / (1 + 1 / (x - 1)) = (x - 1) / x := by
        field_simp [h2, show x ≠ 0 by exact hx1]
        <;> ring_nf
        <;> field_simp [h2, show x ≠ 0 by exact hx1]
        <;> ring
      have h5 : 1 - 1 / (1 + 1 / (x - 1)) = 1 / x := by
        rw [h4]
        field_simp [show x ≠ 0 by exact hx1]
        <;> ring_nf
        <;> field_simp [show x ≠ 0 by exact hx1]
        <;> ring
      rw [h5]
      field_simp [show x ≠ 0 by exact hx1]
    have h2019 : x ≤ 2019 := by
      rw [h1] at hineq
      linarith
    exact ⟨h2019, hx1, hx2⟩
  · -- Assume right side: x ≤ 2019 ∧ x ≠ 0 ∧ x ≠ 1, prove x ≠ 0 ∧ x ≠ 1 ∧ 1 / (1 - 1 / (1 + 1 / (x - 1))) ≤ 2019
    intro h
    rcases h with ⟨h2019, hx1, hx2⟩
    constructor
    · exact hx1
    constructor
    · exact hx2
    · -- Let's show that 1 / (1 - 1 / (1 + 1 / (x - 1))) = x.
      have h1 : 1 / (1 - 1 / (1 + 1 / (x - 1))) = x := by
        have h2 : x - 1 ≠ 0 := by
          intro h'
          have : x = 1 := by linarith
          tauto
        have h4 : 1 / (1 + 1 / (x - 1)) = (x - 1) / x := by
          field_simp [h2, show x ≠ 0 by exact hx1]
          <;> ring_nf
          <;> field_simp [h2, show x ≠ 0 by exact hx1]
          <;> ring
        have h5 : 1 - 1 / (1 + 1 / (x - 1)) = 1 / x := by
          rw [h4]
          field_simp [show x ≠ 0 by exact hx1]
          <;> ring_nf
          <;> field_simp [show x ≠ 0 by exact hx1]
          <;> ring
        rw [h5]
        field_simp [show x ≠ 0 by exact hx1]
      rw [h1]
      all_goals linarith