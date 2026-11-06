import Mathlib

theorem inequalities_289495 :
    Set.ncard {A : Finset ℕ | A ⊆ Finset.Icc 1 7 ∧ A.Nonempty ∧ ∀ a ∈ A, 8 - a ∈ A} = 15 := by
  have h1 : {A : Finset ℕ | A ⊆ Finset.Icc 1 7 ∧ A.Nonempty ∧ ∀ a ∈ A, 8 - a ∈ A} = Finset.filter (fun A => A.Nonempty ∧ ∀ a ∈ A, 8 - a ∈ A) (Finset.powerset (Finset.Icc 1 7)) := by
    ext A
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide