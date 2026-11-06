import Mathlib

theorem negated_number_theory_51362 :
    ∃ (m : ℕ), 
    m ≥ 3 ∧ ∃ S : Finset ℕ, S ⊆ Finset.Icc 0 98 ∧ S.card = m ∧ ∀ x ∈ S, ∀ y ∈ S, ∃ z ∈ S, x + y ≡ 2 * z [ZMOD 99] ↔ m = 3 ∨ m = 9 ∨ m = 11 ∨ m = 33 ∨ m = 99 := by
  use 99
  constructor 
  · -- Show m >= 3
    norm_num
  · -- Use Finset.Icc 0 98 for S 
    use Finset.Icc 0 98
    simp [Finset.mem_Icc]
    native_decide