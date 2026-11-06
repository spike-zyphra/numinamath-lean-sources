import Mathlib

theorem number_theory_95954 :
    Set.ncard {n : ℕ | n ≤ 24 ∧ ∑ i ∈ Finset.Icc 1 n, i ∣ Nat.factorial n} = 16 := by 
  have h : {n : ℕ | n ≤ 24 ∧ ∑ i ∈ Finset.Icc 1 n, i ∣ Nat.factorial n} = Finset.filter (fun n => ∑ i ∈ Finset.Icc 1 n, i ∣ Nat.factorial n) (Finset.Iic 24) := by 
    ext n
    simp 
    <;> aesop

  rw [h]
  rw [Set.ncard_coe_Finset]
  native_decide