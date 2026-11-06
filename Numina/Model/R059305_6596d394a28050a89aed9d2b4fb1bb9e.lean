import Mathlib

open Set Real

theorem inequalities_226894 (m : ℝ) (B : Set ℝ) (hB : B = {x | m + 1 ≤ x ∧ x ≤ 2 * m - 1}) :
    B ⊆ {x | -2 ≤ x ∧ x ≤ 5} ↔ m ≤ 3 := by
  constructor
  · -- Assume B ⊆ {x | -2 ≤ x ∧ x ≤ 5}, prove m ≤ 3
    intro h
    by_contra h1
    push_neg at h1
    have h2 : m > 3 := by linarith
    have h3 : 2 * m - 1 > (5 : ℝ) := by linarith
    -- Show 2m-1 ∈ B.
    have h4 : (2 * m - 1 : ℝ) ∈ B := by
      rw [hB]
      constructor
      · -- Show m + 1 ≤ 2m - 1.
        nlinarith
      · -- Show 2m - 1 ≤ 2m - 1.
        all_goals linarith
    -- So 2m-1 ∈ A.
    have h5 : (2 * m - 1 : ℝ) ∈ ({x | -2 ≤ x ∧ x ≤ 5} : Set ℝ) := by
      apply h
      exact h4
    simp at h5
    linarith -- contradiction
  · -- Assume m ≤ 3, prove B ⊆ {x | -2 ≤ x ∧ x ≤ 5}
    intro hm x hx
    have hB' : x ∈ B := hx
    rw [hB] at hB'
    have hm1 : m + 1 ≤ (x : ℝ) := hB'.1
    have hm2 : (x : ℝ) ≤ 2 * m - 1 := hB'.2
    constructor
    · -- Show -2 ≤ (x : ℝ)
      nlinarith
    · -- Show (x : ℝ) ≤ 5
      nlinarith