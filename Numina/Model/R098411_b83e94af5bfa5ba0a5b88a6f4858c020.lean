import Mathlib

theorem number_theory_196181 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ 6 ∣ n ∧ (n % 10) + (n / 100) = 2 * ((n / 10) % 10)} = 20 := by 
  have : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ 6 ∣ n ∧ (n % 10) + (n / 100) = 2 * ((n / 10) % 10)} = Finset.filter (fun n => 6 ∣ n ∧ (n % 10) + (n / 100) = 2 * ((n / 10) % 10)) (Finset.Icc 100 999) := by 
    ext n 
    simp 
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide