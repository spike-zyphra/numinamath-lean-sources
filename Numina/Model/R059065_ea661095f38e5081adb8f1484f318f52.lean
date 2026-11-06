import Mathlib

theorem number_theory_98151 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ Odd n ∧ 3 ∣ n ∧ ¬(∃ d ∈ Nat.digits 10 n, d = 3)} = 96 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ Odd n ∧ 3 ∣ n ∧ ¬(∃ d ∈ Nat.digits 10 n, d = 3)} = Finset.filter (fun n => Odd n ∧ 3 ∣ n ∧ ¬(∃ d ∈ Nat.digits 10 n, d = 3)) (Finset.Icc 100 999) := by 
    ext n 
    simp 
    <;> try { simp [Nat.odd_iff] }
    <;> try { tauto }
  
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide