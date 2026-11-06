import Mathlib

theorem number_theory_288720 : {n : ℕ | n ∈ Finset.Icc 1 90 ∧ ¬(3 ∣ n) ∧ ¬(5 ∣ n)}.ncard = 48 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 90 ∧ ¬(3 ∣ n) ∧ ¬(5 ∣ n)} = Finset.filter (fun n => ¬(3 ∣ n) ∧ ¬(5 ∣ n)) (Finset.Icc 1 90) := by
    ext n
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide