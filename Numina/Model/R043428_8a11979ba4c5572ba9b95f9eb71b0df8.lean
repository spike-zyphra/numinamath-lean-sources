import Mathlib

theorem algebra_138281 {G H : Type*} [Group G] [Group H]
    (φ : G →* H) : ∃ K : Subgroup H, (Set.range φ) = K := by
  use φ.range
  all_goals
    ext x
    simp