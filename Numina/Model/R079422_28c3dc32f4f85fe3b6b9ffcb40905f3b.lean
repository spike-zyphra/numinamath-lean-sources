import Mathlib

theorem algebra_231181 (S : Finset ℤ) (hS : S = {-5, -3, -1, 2, 4, 6}) :
    IsLeast {x | ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x = a * b * c ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S} (-120) := by
  rw [hS]
  constructor
  · -- First, we need to show that -120 is achievable.
    use -5, 4, 6
    all_goals simp [Finset.mem_insert, Finset.mem_singleton]
    <;> norm_num
    <;> tauto
  · -- Now, we need to show minimality. Any number in the set is ≥ -120.
    rintro x ⟨a, b, c, hab, hac, b_ac, h_eq, ha, hb, hc⟩
    simp [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl)
    <;> rcases hb with (rfl | rfl | rfl | rfl | rfl | rfl)
    <;> rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl)
    <;> omega