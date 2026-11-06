import Mathlib

theorem number_theory_128786 : {n : ℤ | n ∈ Finset.Icc (-100) 500 ∧ 11 ∣ (n^3 + 2 * n^2 - 5 * n - 6)}.ncard = 164 := by 
  have h1 : {n : ℤ | n ∈ Finset.Icc (-100) 500 ∧ 11 ∣ (n^3 + 2 * n^2 - 5 * n - 6)} = Finset.filter (λ n => 11 ∣ (n^3 + 2 * n^2 - 5 * n - 6)) (Finset.Icc (-100) 500) := by 
    ext n 
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide