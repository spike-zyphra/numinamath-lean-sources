import Mathlib

theorem number_theory_156932 :
    Set.ncard {n : ℕ | 1 ≤ n ∧ n < 200 ∧ ∑ p in n.primeFactors, p = 16} = 6 := by 
  have h1 : {n : ℕ | 1 ≤ n ∧ n < 200 ∧ ∑ p in n.primeFactors, p = 16} = 
      Finset.filter (fun n => 1 ≤ n ∧ n < 200 ∧ ∑ p in n.primeFactors, p = 16) (Finset.Icc 0 199) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide