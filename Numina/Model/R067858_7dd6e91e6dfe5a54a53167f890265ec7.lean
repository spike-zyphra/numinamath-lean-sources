import Mathlib

theorem number_theory_180939 :
    Set.ncard {n : ℕ | n < 1000 ∧ ¬(7 ∣ n ∨ 11 ∣ n)} = 779 := by 
  have h1 : {n : ℕ | n < 1000 ∧ ¬(7 ∣ n ∨ 11 ∣ n)} = Finset.filter (fun n => n < 1000 ∧ ¬(7 ∣ n ∨ 11 ∣ n)) (Finset.Icc 0 999) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide