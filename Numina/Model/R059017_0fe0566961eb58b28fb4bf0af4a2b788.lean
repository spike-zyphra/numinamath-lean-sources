import Mathlib

theorem number_theory_274834 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 5000 6000 ∧ n / 1000 = (n / 100) % 10 + (n / 10) % 10 + (n % 10)} = 21 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 5000 6000 ∧ n / 1000 = (n / 100) % 10 + (n / 10) % 10 + (n % 10)} = Finset.filter (fun n => n / 1000 = (n / 100) % 10 + (n / 10) % 10 + (n % 10)) (Finset.Icc 5000 6000) := by 
    ext n 
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide