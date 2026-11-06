import Mathlib

theorem number_theory_155221 :
    Set.ncard {n : ℕ | Even n ∧ 1 ≤ n ∧ n ≤ 2020 ∧ 9 ∈ Nat.digits 10 n} = 190 := by 
  have h1 : {n : ℕ | Even n ∧ 1 ≤ n ∧ n ≤ 2020 ∧ 9 ∈ Nat.digits 10 n} = Finset.filter (fun n => Even n ∧ 1 ≤ n ∧ n ≤ 2020 ∧ 9 ∈ Nat.digits 10 n) (Finset.Icc 0 2020) := by 
    ext n
    simp 
    <;> omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide