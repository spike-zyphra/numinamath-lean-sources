import Mathlib

def A : Finset ℕ := Finset.Icc 1 99
def B : Finset ℕ := A.image (fun x => 2 * x)
def C : Finset ℕ := A.filter (fun x => 2 * x ∈ A)

theorem number_theory_184722 : (B ∩ C).card = 24 := by
  native_decide