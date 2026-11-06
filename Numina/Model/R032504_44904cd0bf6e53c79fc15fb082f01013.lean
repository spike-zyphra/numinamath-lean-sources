import Mathlib

theorem algebra_9036 (m : ℝ) :{x | x ^ 2 - x ≤ 0} ⊆ {x | x ^ 2 - 4 * x + m ≥ 0} ↔ m ≥ 3 := by
  constructor
  · -- Forward implication: if {x | x^2 - x ≤ 0} ⊆ {x | x^2 - 4x + m ≥ 0}, then m ≥ 3
    intro h
    have h1 : (1 : ℝ) ^ 2 - (1 : ℝ) ≤ 0 := by norm_num
    have h2 : (1 : ℝ) ∈ {x | x ^ 2 - 4 * x + m ≥ 0} := by
      apply h
      norm_num
    simp at h2
    linarith
  · -- Backward implication: if m ≥ 3, then {x | x^2 - x ≤ 0} ⊆ {x | x^2 - 4x + m ≥ 0}
    intro hm x hx
    have h3 : x ^ 2 - x ≤ 0 := by
      simpa using hx
    have h4 : 0 ≤ x := by
      nlinarith
    have h5 : x ≤ 1 := by
      nlinarith
    have h6 : x ^ 2 - 4 * x + m ≥ 0 := by
      nlinarith
    simpa using h6