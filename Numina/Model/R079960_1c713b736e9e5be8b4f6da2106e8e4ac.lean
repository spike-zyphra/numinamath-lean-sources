import Mathlib

set_option maxHeartbeats 500000

theorem number_theory_4117 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧
    (Nat.digits 10 n).prod % 10 ≠ 0}.ncard = 4465 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧
      (Nat.digits 10 n).prod % 10 ≠ 0} = Finset.filter (fun n => (Nat.digits 10 n).prod % 10 ≠ 0) (Finset.Icc 1000 9999) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide