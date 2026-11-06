import Mathlib

theorem number_theory_222502 :
    Set.ncard {m : ℕ | m ∈ Finset.Icc 1 1996 ∧ ¬Nat.Coprime (m ^ 2 + 7) (m + 4)} = 86 := by
  have h1 : {m : ℕ | m ∈ Finset.Icc 1 1996 ∧ ¬Nat.Coprime (m ^ 2 + 7) (m + 4)} = Finset.filter (fun m => ¬Nat.Coprime (m ^ 2 + 7) (m + 4)) (Finset.Icc 1 1996) := by
    ext m
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide