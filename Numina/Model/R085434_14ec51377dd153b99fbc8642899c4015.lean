import Mathlib

theorem number_theory_161820 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 200 ∧ ∑ p in n.primeFactors, p = 16} = 6 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 200 ∧ ∑ p in n.primeFactors, p = 16} = Finset.filter (fun n => ∑ p in n.primeFactors, p = 16) (Finset.Icc 1 200) := by 
    ext n 
    simp 
  rw [h1] 
  rw [Set.ncard_coe_Finset]
  native_decide