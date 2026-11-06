import Mathlib

def isClever (n : ℕ) := n = 4 * (Nat.digits 10 n).sum

theorem number_theory_957 :
    Set.ncard {n | ¬isClever n ∧ n ∈ Finset.Icc 10 99} = 86 := by 
  have h1 : {n | ¬isClever n ∧ n ∈ Finset.Icc 10 99} = 
      Finset.filter (fun n => n ≠ 4 * (Nat.digits 10 n).sum) (Finset.Icc 10 99) := by 
    ext n
    simp [isClever]
    <;> aesop 
  rw [h1] 
  rw [Set.ncard_coe_Finset] 
  native_decide