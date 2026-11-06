import Mathlib

set_option maxHeartbeats 500000
theorem algebra_12833 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).contains 7} = 18 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (Nat.digits 10 n).contains 7} = Finset.filter (λ n => (Nat.digits 10 n).contains 7) (Finset.Icc 10 99) := by
    ext n 
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide