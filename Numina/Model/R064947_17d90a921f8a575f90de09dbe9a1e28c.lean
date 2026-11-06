import Mathlib

theorem algebra_138291 {G H : Type*} [Group G] [Group H]
    (φ : G →* H) : ∃ K : Subgroup G, ∀ x : G, φ x = 1 ↔ x ∈ K := by 
  use φ.ker
  intro x
  simp [φ.mem_ker]