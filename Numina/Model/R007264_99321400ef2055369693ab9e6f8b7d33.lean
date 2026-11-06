import Mathlib

theorem number_theory_112423 : {n : ℕ | n ∈ Finset.Icc 1 500 ∧ (3 ∣ n ∨ 7 ∣ n)}.ncard = 214 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 500 ∧ (3 ∣ n ∨ 7 ∣ n)} = Finset.filter (fun n => 3 ∣ n ∨ 7 ∣ n) (Finset.Icc 1 500) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide