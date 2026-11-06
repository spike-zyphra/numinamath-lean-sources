import Mathlib

theorem number_theory_205029 :
    Set.ncard {m : ℕ | 0 < m ∧ m ≤ 1000 ∧ Nat.Coprime (m + 4) (m ^ 2 + 7)} = 957 := by
  have h1 : {m : ℕ | 0 < m ∧ m ≤ 1000 ∧ Nat.Coprime (m + 4) (m ^ 2 + 7)} = Finset.filter (fun m => 0 < m ∧ m ≤ 1000 ∧ Nat.Coprime (m + 4) (m ^ 2 + 7)) (Finset.Icc 0 1000) := by 
    ext m
    simp 
    <;> omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide