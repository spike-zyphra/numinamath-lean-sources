import Mathlib

theorem algebra_21716 (alphabet : Set Char) (ha : alphabet = {'A', 'B', 'C'}) :
    (Set.univ : Set (alphabet × alphabet × alphabet)).ncard = 27 := by
  rw [ha]
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.card_univ]
  <;> native_decide