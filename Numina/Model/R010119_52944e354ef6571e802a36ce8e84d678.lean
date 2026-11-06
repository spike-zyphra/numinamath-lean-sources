import Mathlib

  theorem number_theory_2503 :
  Set.ncard {n : ℕ | n ∈ Finset.Icc 1 1000 ∧ (10 ∣ n ∨ 15 ∣ n ∨ 25 ∣ n)} = 146 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 1000 ∧ (10 ∣ n ∨ 15 ∣ n ∨ 25 ∣ n)} = Finset.filter (fun n => (10 ∣ n ∨ 15 ∣ n ∨ 25 ∣ n)) (Finset.Icc 1 1000) := by
    ext n
    simp 
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide