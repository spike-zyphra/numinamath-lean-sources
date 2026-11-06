import Mathlib

theorem calculus_23202 : Set.range (fun (t : ℝ) ↦ 2 * Real.cos t) = Set.range (fun (s : Set.Icc (-2) 0) ↦ 2 * s.1 + 2) := by
  ext y
  simp [Set.mem_range]
  constructor
  · -- Assume $y \in \text{range} (2 \cos t)$, need to show $y \in \text{range} (2s + 2)$.
    intro hy
    rcases hy with ⟨t, ht⟩
    have h1 : -2 ≤ y ∧ y ≤ 2 := by
      constructor
      · -- Show -2 ≤ y
        have hcos1 : -1 ≤ Real.cos t := Real.neg_one_le_cos t
        nlinarith
      · -- Show y ≤ 2
        have hcos2 : Real.cos t ≤ 1 := Real.cos_le_one t
        nlinarith
    use (y - 2) / 2
    constructor
    · -- Show that -2 ≤ (y - 2) / 2 ≤ 0
      constructor
      · -- Show -2 ≤ (y - 2) / 2
        linarith
      · -- Show (y - 2) / 2 ≤ 0
        linarith
    · -- Show equality
      nlinarith
  · -- Assume $y \in \text{range} (2s + 2)$, need to show $y \in \text{range} (2 \cos t)$.
    intro h
    rcases h with ⟨s, ⟨hs1, hs2⟩, ht⟩
    use Real.arccos (y / 2)
    have h1 : -1 ≤ y / 2 ∧ y / 2 ≤ 1 := by
      constructor
      · -- Show -1 ≤ y / 2
        linarith
      · -- Show y / 2 ≤ 1
        linarith
    have hcos : Real.cos (Real.arccos (y / 2)) = y / 2 := by
      apply Real.cos_arccos
      all_goals
        linarith
    linarith