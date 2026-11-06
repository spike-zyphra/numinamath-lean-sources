import Mathlib

open Set Real

theorem algebra_328370 {a : ℝ} (ha : 2 * a + 1 ≤ 3 * a - 5) :
    {x | 2 * a + 1 ≤ x ∧ x ≤ 3 * a - 5} ⊆ {x | 3 ≤ x ∧ x ≤ 22} ↔
    6 ≤ a ∧ a ≤ 9 := by
  constructor
  · -- Forward direction: If {x | 2a+1 ≤ x ∧ x ≤ 3a-5} ⊆ {x | 3 ≤ x ∧ x ≤ 22}, then 6 ≤ a ∧ a ≤ 9
    intro h
    have h1 : 2 * a + 1 ≤ 3 * a - 5 := by linarith [ha]
    have ha1 : a ≥ 6 := by linarith
    -- Show that the right end point of A is less than 22
    have h2 : 3 * a - 5 ≤ 22 := by
      have h2 : 3 * a - 5 ∈ {x | 2 * a + 1 ≤ x ∧ x ≤ 3 * a - 5} := by
        simp
        all_goals linarith [ha]
      have h3 : (3 * a - 5) ∈ {x | 3 ≤ x ∧ x ≤ 22} := h h2
      simp at h3
      all_goals linarith [h3]
    -- From the right end point constraint
    have ha2 : a ≤ 9 := by linarith
    -- Finalizing the desired result
    exact ⟨by linarith, by linarith⟩
  · -- Backward direction: If 6 ≤ a ∧ a ≤ 9, then {x | 2a+1 ≤ x ∧ x ≤ 3a-5} ⊆ {x | 3 ≤ x ∧ x ≤ 22}
    rintro ⟨ha1, ha2⟩
    intro x hx
    rcases hx with ⟨hd1, hd2⟩
    -- Need to show 3 ≤ x ∧ x ≤ 22 from 2a+1 ≤ x ∧ x ≤ 3a-5
    exact ⟨by nlinarith, by nlinarith⟩