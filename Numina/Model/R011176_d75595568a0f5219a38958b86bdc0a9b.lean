import Mathlib

theorem number_theory_611460 :
    {n ∈ Finset.Icc 10 1000 | ¬10 ∣ n ∧ 7 ∣ n ∧ 7 ∣ Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))}.card = 17 := by
  have : {n ∈ Finset.Icc 10 1000 | ¬10 ∣ n ∧ 7 ∣ n ∧ 7 ∣ Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))} = 
          Finset.filter (fun n => ¬10 ∣ n ∧ 7 ∣ n ∧ 7 ∣ Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) (Finset.Icc 10 1000) := by
    ext n 
    simp 
  rw [this] 
  rw [Finset.filter] 
  simp [Finset.Icc]
  <;> native_decide