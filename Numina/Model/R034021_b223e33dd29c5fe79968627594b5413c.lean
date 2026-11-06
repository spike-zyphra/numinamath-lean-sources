import Mathlib

theorem number_theory_190893 : {n : ℕ | n ∈ Finset.Icc 1 2005 ∧ Nat.factorial n ∣ ∏ i ∈ Finset.range n, (4 * i + 2)}.ncard = 2005 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 2005 ∧ Nat.factorial n ∣ ∏ i ∈ Finset.range n, (4 * i + 2)} = Finset.filter (fun n => Nat.factorial n ∣ ∏ i ∈ Finset.range n, (4 * i + 2)) (Finset.Icc 1 2005) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide