import Mathlib

theorem number_theory_3381 :
  ∃r : Finset ℕ, r = {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 5 ∣ ∑ i in Finset.Icc 1 n, i} ∧ 
  r.sum id = 1962 := by 
  have h₁ : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 5 ∣ ∑ i in Finset.Icc 1 n, i} = Finset.filter (fun n => 5 ∣ ∑ i in Finset.Icc 1 n, i) (Finset.Icc 10 99) := by 
    ext n
    simp 
  use Finset.filter (fun n => 5 ∣ ∑ i in Finset.Icc 1 n, i) (Finset.Icc 10 99)
  constructor 
  · -- Show r = {n : ℕ | n ∈ Finset.Icc 10 99 ∧ 5 ∣ ∑ i in Finset.Icc 1 n, i}
    rw [h₁]
  · -- Compute r.sum
    native_decide