import Mathlib

theorem number_theory_283178 :
    Set.ncard {n : ℕ | n < 1000 ∧ ¬5 ∣ n ∧ ¬7 ∣ n} = 686 := by 
  have h1 : {n : ℕ | n < 1000 ∧ ¬5 ∣ n ∧ ¬7 ∣ n} = Finset.filter (fun n => n < 1000 ∧ ¬5 ∣ n ∧ ¬7 ∣ n) (Finset.Icc 0 999) := by 
    ext n 
    simp 
    <;> omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide