import Mathlib

theorem algebra_13702 :
    {n | n ∈ Finset.Icc 1 53 ∧ (54 - n) % 10 = n % 10}.ncard = 11 := by
  have h1 : {n | n ∈ Finset.Icc 1 53 ∧ (54 - n) % 10 = n % 10} = 
    Finset.filter (fun x => (54 - x) % 10 = x % 10) (Finset.Icc 1 53) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide