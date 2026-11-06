import Mathlib

def is_symmetric (n : ℕ) := Nat.digits 10 n = List.reverse (Nat.digits 10 n)

theorem number_theory_131271 :
    Set.ncard {n | n ∈ Finset.Icc 1000000 9999999 ∧ is_symmetric n ∧ is_symmetric (n + 1100)} = 810 := by 
  have h3 : {n | n ∈ Finset.Icc 1000000 9999999 ∧ is_symmetric n ∧ is_symmetric (n + 1100)} = 
      Finset.filter (fun n => (Nat.digits 10 n = List.reverse (Nat.digits 10 n)) ∧ (Nat.digits 10 (n + 1100) = List.reverse (Nat.digits 10 (n + 1100)))) (Finset.Icc 1000000 9999999) := by 
    ext n
    simp [is_symmetric, Finset.mem_Icc]
    <;> aesop 
    <;> try { tauto }
  rw [h3]
  rw [Set.ncard_coe_Finset]
  native_decide