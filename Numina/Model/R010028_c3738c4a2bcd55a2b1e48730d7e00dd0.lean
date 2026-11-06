import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_15424 :
  {x : ℝ | x - 2 ≥ 0 ∧ 5 - x ≥ 0 ∧ √(5 - x) ≠ 0} = Ico 2 5 := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · -- First direction: {x : ℝ | x - 2 ≥ 0 ∧ 5 - x ≥ 0 ∧ √(5 - x) ≠ 0} → [2, 5)
    intro h
    rcases h with ⟨h1, h2, h3⟩
    constructor
    · -- Show that 2 ≤ x
      linarith
    · -- Show that x < 5
      by_contra h
      push_neg at h
      have h6 : x ≥ 5 := by linarith
      have h7 : 5 - x ≤ 0 := by linarith
      have h8 : 5 - x = 0 := by linarith [h2, h7]
      have h9 : √(5 - x) = 0 := by
        rw [show 5 - x = 0 by linarith [h8]]
        norm_num [Real.sqrt_eq_zero]
      contradiction
  · -- Second direction: [2, 5) → {x : ℝ | x - 2 ≥ 0 ∧ 5 - x ≥ 0 ∧ √(5 - x) ≠ 0}
    intro h
    rcases h with ⟨h1, h2⟩
    constructor
    · -- Show that x - 2 ≥ 0
      linarith
    constructor
    · -- Show that 5 - x ≥ 0
      linarith
    · -- Show that √(5 - x) ≠ 0
      have h4 : 5 - x > 0 := by linarith
      have h5 : √(5 - x) > 0 := by
        apply Real.sqrt_pos.2
        linarith
      intro h
      linarith [h5, h, Real.sqrt_nonneg (5 - x)]