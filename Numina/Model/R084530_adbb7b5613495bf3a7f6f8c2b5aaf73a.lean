import Mathlib

theorem number_theory_96781 :
    Set.ncard {N : ℕ | N ∈ Finset.Icc 1 1990 ∧ ¬(Nat.Coprime (N ^ 2 + 7) (N + 4))} = 86 := by 
  have h1 : {N : ℕ | N ∈ Finset.Icc 1 1990 ∧ ¬(Nat.Coprime (N ^ 2 + 7) (N + 4))} = Finset.filter (fun N => ¬(Nat.Coprime (N ^ 2 + 7) (N + 4))) (Finset.Icc 1 1990) := by
    ext N
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide