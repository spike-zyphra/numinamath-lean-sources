import Mathlib

theorem number_theory_168306 :
    Set.ncard {n : ℕ | n ≤ 1000000 ∧ Nat.mod n 1000 > Nat.mod n 1001} = 499500 := by
  have h1 : {n : ℕ | n ≤ 1000000 ∧ Nat.mod n 1000 > Nat.mod n 1001} = Finset.filter (fun n => Nat.mod n 1000 > Nat.mod n 1001) (Finset.Iic 1000000) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide