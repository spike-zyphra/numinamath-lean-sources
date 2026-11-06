import Mathlib

theorem algebra_94607 (S : Finset ℤ) (hS : S = {-8, -6, -4, 0, 3, 5, 7}) :
    IsLeast {x | ∃ a b c, x = a * b * c ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c} (-280) := by 
  constructor
  · -- Show that -280 is a possible product
    use -8, 5, 7
    norm_num [hS]
  · -- Show that any element in the set is at least -280
    intro x hx
    rcases hx with ⟨a, b, c, h_eq, ha, hb, hc, h1, h2, h3⟩
    rw [hS] at ha hb hc
    simp at ha hb hc
    rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    <;> rcases hb with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    <;> rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    <;> norm_num at h_eq <;> omega