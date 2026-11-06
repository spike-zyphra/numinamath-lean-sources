import Mathlib

def s : Finset ℕ := {1, 2, 3, 5, 8, 13, 21, 34, 55}

theorem number_theory_266594 :
    Set.ncard {x | 3 ≤ x ∧ x ≤ 89 ∧ ¬∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ a + b = x} = 51 := by 
  have h1 : {x | 3 ≤ x ∧ x ≤ 89 ∧ ¬∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ a + b = x} = 
    Finset.filter (fun x => 3 ≤ x ∧ x ≤ 89 ∧ ¬∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ a + b = x) (Finset.Icc 0 89) := by
    ext x
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide