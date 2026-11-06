import Mathlib

open Set Real

theorem inequalities_321292 (a : ℝ) :
    {x | 2 * a + 1 ≤ x ∧ x ≤ 3 * a + 5} ⊆ {x | 3 ≤ x ∧ x ≤ 33} ↔
    a < -4 ∨ a ∈ Icc 1 (28 / 3) := by
  constructor
  · -- Forward direction: If {x | 2 * a + 1 ≤ x ∧ x ≤ 3 * a + 5} ⊆ {x | 3 ≤ x ∧ x ≤ 33}, then a < -4 ∨ a ∈ Icc 1 (28 / 3)
    intro h
    by_cases h1 : 2 * a + 1 ≤ 3 * a + 5
    · -- If 2 * a + 1 ≤ 3 * a + 5, then $A$ is not empty.
      have ha1 : a ≥ -4 := by linarith
      have h2 : 3 ≤ 2 * a + 1 := by
        -- The element `2 * a + 1` is in the left set, so must satisfy the right set.
        have h2 : (2 * a + 1 : ℝ) ≥ 2 * a + 1 := by linarith
        have h3 : (2 * a + 1 : ℝ) ≤ 3 * a + 5 := by linarith
        have h4 : 3 ≤ (2 * a + 1 : ℝ) := by
          -- `h` is the subset hypothesis, which needs to be applied to elements in the left set.
          have h5 : (2 * a + 1 : ℝ) ∈ {x | 2 * a + 1 ≤ x ∧ x ≤ 3 * a + 5} := by
            exact ⟨by linarith, by linarith⟩
          have h6 : (2 * a + 1 : ℝ) ∈ {x | 3 ≤ x ∧ x ≤ 33} := h h5
          exact h6.left
        linarith
      have h3 : 3 * a + 5 ≤ 33 := by
        have h8 : (3 * a + 5 : ℝ) ≥ 2 * a + 1 := by linarith
        have h9 : (3 * a + 5 : ℝ) ≤ 3 * a + 5 := by linarith
        have h10 : (3 * a + 5 : ℝ) ∈ {x | 2 * a + 1 ≤ x ∧ x ≤ 3 * a + 5} := by
          exact ⟨by linarith, by linarith⟩
        have h11 : (3 * a + 5 : ℝ) ∈ {x | 3 ≤ x ∧ x ≤ 33} := h h10
        have h12 : (3 * a + 5 : ℝ) ≤ 33 := h11.right
        linarith
      have ha2 : a ≥ 1 := by linarith
      have ha3 : a ≤ 28 / 3 := by linarith
      right
      exact ⟨by linarith, by linarith⟩
    · -- If A is empty, then $a < -4$, which is true.
      push_neg at h1
      have : a < -4 := by linarith
      left
      linarith
  · -- Backward direction: If a < -4 ∨ a ∈ Icc 1 (28 / 3), then {x | 2 * a + 1 ≤ x ∧ x ≤ 3 * a + 5} ⊆ {x | 3 ≤ x ∧ x ≤ 33}
    rintro (h | h)
    · -- If a < -4, then $A$ is empty.
      have h1 : 2 * a + 1 > 3 * a + 5 := by linarith
      intro x hx
      have h11 : 2 * a + 1 ≤ x := hx.1
      have h12 : x ≤ 3 * a + 5 := hx.2
      linarith
    · -- If a ∈ [1, 28/3], then endpoints will be in B.
      rcases h with ⟨h2, h3⟩
      intro x hx
      have h21 : 2 * a + 1 ≤ x := hx.1
      have h22 : x ≤ 3 * a + 5 := hx.2
      constructor
      · -- Show that 3 ≤ x
        linarith
      · -- Show that x ≤ 33
        linarith