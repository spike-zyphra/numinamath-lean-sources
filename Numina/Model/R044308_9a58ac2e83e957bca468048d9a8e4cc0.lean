import Mathlib

def A : Finset ℕ := Finset.Icc 1 100
def B : Finset ℕ := Finset.image (fun x => x ^ 2) A

def isAssociated (x : ℕ) : Prop :=
  ∃ y ∈ B, x + y ∈ B

theorem number_theory_303644 :
    {x | x ∈ A ∧ isAssociated x}.ncard = 73 := by
  have h1 : {x | x ∈ A ∧ isAssociated x} = Finset.filter (fun x => ∃ y ∈ B, x + y ∈ B) A := by 
    ext x 
    simp [A, isAssociated, B]
    <;> tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide