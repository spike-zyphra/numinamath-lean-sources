import Mathlib

theorem algebra_255147 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ n % (Nat.digits 10 n).sum = 0 ∧ Odd n} = 5 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ n % (Nat.digits 10 n).sum = 0 ∧ Odd n} = Finset.filter (fun n => n % (Nat.digits 10 n).sum = 0 ∧ Odd n) (Finset.Icc 10 99) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide