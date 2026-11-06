import Mathlib

theorem number_theory_274300 : {n : ℕ | n ∈ Finset.Icc 1 30030 ∧ ∀ k ∈ Finset.Icc 2 16, ¬(k ∣ n)}.ncard = 5760 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 30030 ∧ ∀ k ∈ Finset.Icc 2 16, ¬(k ∣ n)} = Finset.filter (fun n => ∀ k ∈ Finset.Icc 2 16, ¬(k ∣ n)) (Finset.Icc 1 30030) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide